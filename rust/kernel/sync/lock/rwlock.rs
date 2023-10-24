// SPDX-License-Identifier: GPL-2.0

use crate::bindings;
use crate::prelude::*;
use super::{Backend, Lock, LockClassKey, Guard};

use core::mem::transmute;
use core::marker::PhantomData;

#[macro_export]
macro_rules! new_rwlock {
    ($inner:expr $(, $name:literal)? $(,)?) => {
        $crate::sync::RwLock::new(
            $inner, $crate::optional_name!($($name)?), $crate::static_lock_class!())
    };
}

#[repr(transparent)]
#[pin_data]
pub struct RwLock<T> {
    #[pin]
    inner: Lock<T, RwLockBackend<Read>>,
}

#[derive(Debug)]
pub enum LockError {
    TryRead,
    ReadInterruptible,
    ReadKillable,
    TryWrite,
    WriteKillable,
}

impl core::fmt::Display for LockError {
    fn fmt(
        &self,
        fmt: &mut core::fmt::Formatter<'_>,
    ) -> core::result::Result<(), core::fmt::Error> {
        fmt.write_str("lock failed on ")?;
        let reason = match self {
            LockError::TryRead => "down_read_trylock",
            LockError::ReadInterruptible => "down_read_interruptible",
            LockError::ReadKillable => "down_read_killable",
            LockError::TryWrite => "down_write_trylock",
            LockError::WriteKillable => "down_write_killable",
        };
        fmt.write_str(reason)
    }
}

impl<T> RwLock<T> {
    pub fn new(t: T, name: &'static CStr, key: &'static LockClassKey) -> impl PinInit<Self> {
        pin_init!(Self {
            inner <- Lock::new(t, name, key)
        })
    }

    pub fn read(&self) -> Guard<'_, T, RwLockBackend<Read>> {
        let inner: &Lock<T, RwLockBackend<Read>>  = unsafe { transmute(&self.inner) };
        inner.lock()
    }

    pub fn try_read(&self) -> Result<Guard<'_, T, RwLockBackend<TryRead>>, LockError> {
        let inner: &Lock<T, RwLockBackend<TryRead>> = unsafe { transmute(&self.inner) };
        let state = unsafe { RwLockBackend::<TryRead>::lock(inner.state.get()) };
        match state {
            Some(val) if val == 1 => Ok(
                unsafe { Guard::new(inner, state) }
            ),
            _ => Err(LockError::TryRead),
        }
    }

    pub fn read_interruptible(&self) -> Result<Guard<'_, T, RwLockBackend<ReadInterruptible>>, LockError> {
        let inner: &Lock<T, RwLockBackend<ReadInterruptible>> = unsafe { transmute(&self.inner) };
        let state = unsafe { RwLockBackend::<ReadInterruptible>::lock(inner.state.get()) };
        match state {
            Some(val) if val == 0 => Ok(
                unsafe { Guard::new(inner, state) }
            ),
            _ => Err(LockError::ReadInterruptible),
        }
    }

    pub fn read_killable(&self) -> Result<Guard<'_, T, RwLockBackend<ReadKillable>>, LockError> {
        let inner: &Lock<T, RwLockBackend<ReadKillable>> = unsafe { transmute(&self.inner) };
        let state = unsafe { RwLockBackend::<ReadKillable>::lock(inner.state.get()) };
        match state {
            Some(val) if val == 0 => Ok(
                unsafe { Guard::new(inner, state) }
            ),
            _ => Err(LockError::ReadKillable),
        }
    }

    pub fn write(&self) -> Guard<'_, T, RwLockBackend<Write>> {
        let inner: &Lock<T, RwLockBackend<Write>> = unsafe { transmute(&self.inner) };
        inner.lock()
    }

    pub fn try_write(&self) -> Result<Guard<'_, T, RwLockBackend<TryWrite>>, LockError> {
        let inner: &Lock<T, RwLockBackend<TryWrite>> = unsafe { transmute(&self.inner) };
        let state = unsafe { RwLockBackend::<TryWrite>::lock(inner.state.get()) };
        match state {
            Some(val) if val == 1 => Ok(
                unsafe { Guard::new(inner, state) }
            ),
            _ => Err(LockError::TryWrite),
        }
    }

    pub fn write_killable(&self) -> Result<Guard<'_, T, RwLockBackend<WriteKillable>>, LockError> {
        let inner: &Lock<T, RwLockBackend<WriteKillable>> = unsafe { transmute(&self.inner) };
        let state = unsafe { RwLockBackend::<WriteKillable>::lock(inner.state.get()) };
        match state {
            Some(val) if val == 0 => Ok(
                unsafe { Guard::new(inner, state) }
            ),
            _ => Err(LockError::WriteKillable),
        }
    }

    pub fn downgrade<'a>(this: impl Into<Guard<'a, T, RwLockBackend<Write>>>) -> Guard<'a, T, RwLockBackend<Read>> {
        let guard: Guard<'a, T, RwLockBackend<Write>> = this.into();
        unsafe { bindings::downgrade_write(guard.lock.state.get()) };
        let guard: Guard<'a, T, RwLockBackend<Read>> = unsafe { transmute(guard) };
        guard
    }
}

macro_rules! impl_into {
    ($(($($src:ident$(,)?)+) -> $dst:ident,)+) => {
        $($(
            impl<'a, T> Into<Guard<'a, T, RwLockBackend<$dst>>> for Guard<'a, T, RwLockBackend<$src>> {
                fn into(self) -> Guard<'a, T, RwLockBackend<$dst>> {
                    unsafe { transmute(self) }
                }
            }
        )+)+
    };
}

trait BindingLockFn {
    fn lock(ptr: *mut bindings::rw_semaphore) -> Option<core::ffi::c_int>;
    fn unlock(ptr: *mut bindings::rw_semaphore);
}

macro_rules! impl_binding_lock_fn {
    (@lock $fn:ident) => {
        fn lock(ptr: *mut $crate::bindings::rw_semaphore) -> Option<core::ffi::c_int> {
            unsafe { $crate::bindings::$fn(ptr) };
            None
        }
    };
    (@lock $fn:ident, fallible) => {
        fn lock(ptr: *mut $crate::bindings::rw_semaphore) -> Option<core::ffi::c_int> {
            Some(unsafe { $crate::bindings::$fn(ptr) })
        }
    };
    (@unlock $fn:ident) => {
        fn unlock(ptr: *mut $crate::bindings::rw_semaphore) {
            unsafe { $crate::bindings::$fn(ptr) }
        }
    };
    ($(($type:ident, $lock_fn:ident, $unlock_fn:ident $(, $fallible:tt)?),)+) => {
        $(impl BindingLockFn for $type {
            impl_binding_lock_fn!(@lock $lock_fn $(, $fallible)?);
            impl_binding_lock_fn!(@unlock $unlock_fn);
        })+
    };
}

pub struct Read;
pub struct TryRead;
pub struct ReadInterruptible;
pub struct ReadKillable;
pub struct Write;
pub struct TryWrite;
pub struct WriteKillable;

impl_into! {
    (TryRead, ReadInterruptible, ReadKillable) -> Read,
    (TryWrite, WriteKillable) -> Write,
}

impl_binding_lock_fn! {
    (Read, down_read, up_read),
    (TryRead, down_read_trylock, up_read, fallible),
    (ReadInterruptible, down_read_interruptible, up_read, fallible),
    (ReadKillable, down_read_killable, up_read, fallible),
    (Write, down_write, up_write),
    (TryWrite, down_write_trylock, up_write, fallible),
    (WriteKillable, down_write_killable, up_write, fallible),
}

pub struct RwLockBackend<S> {
    _state: PhantomData<S>,
}

// SAFETY: The underlying kernel `struct mutex` object ensures mutual exclusion.
unsafe impl<S: BindingLockFn> super::Backend for RwLockBackend<S> {
    type State = bindings::rw_semaphore;
    type GuardState = Option<core::ffi::c_int>;

    unsafe fn init(
        ptr: *mut Self::State,
        name: *const core::ffi::c_char,
        key: *mut bindings::lock_class_key,
    ) {
        unsafe { bindings::__init_rwsem(ptr, name, key) }
    }

    unsafe fn lock(ptr: *mut Self::State) -> Self::GuardState {
        S::lock(ptr)
    }

    unsafe fn unlock(ptr: *mut Self::State, _guard_state: &Self::GuardState) {
        S::unlock(ptr)
    }
}