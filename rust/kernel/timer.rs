// SPDX-License-Identifier: GPL-2.0

//! Timer.
//!
//! C header: [`include/linux/timer.h`](../../../../include/linux/timer.h).

use crate::{
    bindings,
    str::CStr,
    sync::{Arc, LockClassKey, UniqueArc},
    Opaque,
};

/// Implements the [`TimerAdapter`] trait for a type where its [`Timer`] instance is a field.
///
/// # Examples
///
/// ```
/// # use kernel::timer::Timer;
///
/// struct Example {
///     timer: Timer,
/// }
///
/// kernel::impl_self_timer_adapter!(Example, timer, |_| {});
/// ```
#[macro_export]
macro_rules! impl_self_timer_adapter {
    ($timer_type:ty, $field:ident, $closure:expr) => {
        $crate::impl_timer_adapter!($timer_type, $timer_type, $field, $closure);
    };
}

/// Implements the [`TimerAdapter`] trait for an adapter type.
///
/// # Examples
///
/// ```
/// # use kernel::timer::Timer;
///
/// struct Example {
///     timer: Timer,
/// }
///
/// struct Adapter;
///
/// kernel::impl_timer_adapter!(Adapter, Example, timer, |_| {});
/// ```
#[macro_export]
macro_rules! impl_timer_adapter {
    ($adapter:ty, $timer_type:ty, $field:ident, $closure:expr) => {
        // SAFETY: We use [`offset_of`] to ensure that the field is within the given type, and we
        // also check its type is [`Timer`].
        unsafe impl $crate::timer::TimerAdapter for $adapter {
            type Target = $timer_type;
            const FIELD_OFFSET: isize = $crate::offset_of!(Self::Target, $field);
            #[allow(unreachable_code)]
            fn run(t: &$crate::sync::Arc<Self::Target>) {
                let closure: fn(&$crate::sync::Arc<Self::Target>) = $closure;
                closure(t);
                return;

                // Checks that the type of the field is actually [`Timer`].
                let tmp = core::mem::MaybeUninit::<$timer_type>::uninit();
                // SAFETY: The pointer is valid and aligned, just not initialised; [`addr_of`]
                // ensures that we don't actually read from it (which would be UB) nor create an
                // intermediate reference.
                let _x: *const $crate::timer::Timer =
                    unsafe { core::ptr::addr_of!((*tmp.as_ptr()).$field) };
            }
        }
    };
}

/// Initialises a timer item with the given adapter.
///
/// It automatically defines a literal name and a new lockdep lock class
/// for the timer item, and the default flag is zero.
#[macro_export]
macro_rules! init_timer_item_adapter {
    ($adapter:ty, $timer_container:expr) => {{
        static NAME: &$crate::str::CStr = $crate::c_str!(stringify!($timer_container));
        static CLASS: $crate::sync::LockClassKey = $crate::sync::LockClassKey::new();
        $crate::timer::Timer::init_with_adapter::<$adapter>($timer_container, 0, NAME, &CLASS)
    }};
}

/// Initialises a timer item.
///
/// It automatically defines a literal name and a new lockdep lock class
/// for the timer item, and the default flag is zero.
#[macro_export]
macro_rules! init_timer_item {
    ($timer_container:expr) => {{
        static NAME: &$crate::str::CStr = $crate::c_str!(stringify!($timer_container));
        static CLASS: $crate::sync::LockClassKey = $crate::sync::LockClassKey::new();
        $crate::timer::Timer::init($timer_container, 0, NAME, &CLASS)
    }};
}

/// An adapter for timer items.
///
/// For the most usual case where a type has a [`Timer`] in it and is itself the adapter, it is
/// recommended that they use the [`impl_self_timer_adapter`] or [`impl_timer_adapter`] macros
/// instead of implementing the [`TimerAdapter`] manually. The great advantage is that they don't
/// require any unsafe blocks.
///
/// # Safety
///
/// Implementers must ensure that there is a [`Timer`] instance `FIELD_OFFSET` bytes from the
/// beginning of a valid [`Target`] type. It is normally safe to use the [`crate::offset_of`] macro
/// for this.
pub unsafe trait TimerAdapter {
    /// The type that this timer adapter is meant to use.
    type Target;

    /// The offset, in bytes, from the beginning of [`Self::Target`] to the instance of [`Timer`].
    const FIELD_OFFSET: isize;

    /// Runs when the timer item is expired, and users can reset expiration time by the `delay`
    /// method of the timer item.
    fn run(t: &Arc<Self::Target>);
}

/// A timer item.
///
/// Wraps the kernel's C `struct timer_list`.
///
/// Users must add a field of this type to a structure, then implement [`TimerAdapter`] using the
/// [`impl_self_timer_adapter`] or [`impl_timer_adapter`] macros (recommended). Then users must call
/// either [`Timer::init`] or [`Timer::init_with_adapter`] before call the `delay` method.
///
/// # Examples
///
/// The following example is used to create a timer item and run it several times.
///
/// ```
/// # use kernel::timer::Timer;
/// use core::sync::atomic::{AtomicU32, Ordering};
/// use core::time::Duration;
/// use kernel::sync::UniqueArc;
///
/// struct Example {
///     count: AtomicU32,
///     timer: Timer,
/// }
///
/// kernel::impl_self_timer_adapter!(Example, timer, |e| {
///     let count = e.count.fetch_add(1, Ordering::Relaxed);
///     pr_info!("Called with count={}\n", count);
///
///     // Delay the timer again if the count is less than 10.
///     if count < 10 {
///         e.timer.delay(Duration::from_millis(1000));
///     }
/// });
///
/// let e = UniqueArc::try_new(Example {
///     count: AtomicU32::new(0),
///     // SAFETY: `timer` is initialised below.
///     timer: unsafe { Timer::new() },
/// })?;
///
/// kernel::init_timer_item!(&e);
///
/// // Delay timer for the first time.
/// e.timer.delay(Duration::from_millis(1000));
///
/// # Ok::<(), Error>(())
/// ```
#[repr(transparent)]
pub struct Timer(Opaque<bindings::timer_list>);

// SAFETY: [`Timer`] is just a wrapper for `struct timer_list`, which can be used from any thread.
unsafe impl Send for Timer {}

// SAFETY: [`Timer`] is just a wrapper for `struct timer_list`, which can be used from any thread.
unsafe impl Sync for Timer {}

impl Timer {
    /// Creates a new instance of [`Timer`].
    ///
    /// # Safety
    ///
    /// Callers must call either [`Timer::init`] or [`Timer::init_with_adapter`] before the timer item
    /// can be used.
    pub unsafe fn new() -> Self {
        Self(Opaque::new(bindings::timer_list::default()))
    }

    /// Initialises the timer item.
    ///
    /// Users should prefer the [`init_timer_item`] macro because it automatically defines a literal
    /// name and a new lockdep lock class. If any TIMER_* flags should be specified, call either
    /// [`Timer::init`] or [`Timer::init_with_adapter`] manually.
    pub fn init<T: TimerAdapter<Target = T>>(
        obj: &UniqueArc<T>,
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) {
        Self::init_with_adapter::<T>(obj, flags, name, key)
    }

    /// Initialises the timer item.
    ///
    /// Users should prefer the [`init_timer_item_adapter`] macro because it automatically defines a
    /// literal name and a new lockdep lock class. If any TIMER_* flags should be specified, call
    /// either [`Timer::init`] or [`Timer::init_with_adapter`] manually.
    pub fn init_with_adapter<A: TimerAdapter>(
        obj: &UniqueArc<A::Target>,
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) {
        let ptr = &**obj as *const _ as *const u8;
        let field_ptr = ptr.wrapping_offset(A::FIELD_OFFSET) as *mut bindings::timer_list;

        // SAFETY: `timer` is valid for writes -- the [`UniqueArc`] instance guarantees that it has
        // been allocated and there is only one pointer to it. Additionally, `timer_func` is a valid
        // callback for the timer item.
        unsafe {
            bindings::init_timer_key(
                field_ptr,
                Some(Self::timer_func::<A>),
                flags as core::ffi::c_uint,
                name.as_char_ptr(),
                key.get(),
            )
        };
    }

    /// Delays the timer item.
    ///
    /// Update the expiration time of an active timer (if the timer is inactive it will be activated).
    /// If there are multiple unserialized concurrent users of the same timer, `mod_timer` is also the
    /// safe way to modify the timeout.
    pub fn delay(&self, time: core::time::Duration) {
        let msecs = time.as_millis() as core::ffi::c_uint;

        // SAFETY: If the timer is uninitialised, this start operation of `mod_timer`is silently discarded.
        // Once it‘s initialised either by [`Timer::init`] or by [`Timer::init_with_adapter`], it is valid.
        unsafe {
            bindings::mod_timer(
                self.0.get(),
                bindings::jiffies + bindings::__msecs_to_jiffies(msecs),
            )
        };
    }

    unsafe extern "C" fn timer_func<A: TimerAdapter>(timer: *mut bindings::timer_list) {
        let field_ptr = timer as *const _ as *const u8;
        let ptr = field_ptr.wrapping_offset(-A::FIELD_OFFSET) as *const A::Target;

        // SAFETY: This callback is only ever used by the [`Timer::init_with_adapter`] method, so it is
        // always the case that the timer item is embedded in a [`Timer`] (Self) struct.
        let t = unsafe { Arc::from_raw(ptr) };
        A::run(&t);
        // SAFETY: We should not drop the [`Target`] struct, since it may be used in next callback.
        core::mem::forget(t);
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        // SAFETY: Once it‘s initialised either by [`Timer::init`] or by [`Timer::init_with_adapter`],
        // it is valid. It is also ok to shutdown a uninitialised timer (`bindings::timer_list::default`)
        // or an activated timer.
        unsafe { bindings::timer_shutdown_sync(self.0.get()) };
    }
}
