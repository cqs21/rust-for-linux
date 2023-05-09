// SPDX-License-Identifier: GPL-2.0

//! Scatterlist.
//!
//! C header: [`include/linux/scatterlist.h`](../../../../include/linux/scatterlist.h)
//!
//! Reference: <https://www.kernel.org/doc/html/latest/crypto/api-intro.html>

use crate::error::{Error, Result};
use crate::prelude::*;
use crate::types::Opaque;
use crate::{new_mutex, sync::Mutex};
use core::marker::PhantomPinned;

/// A simple array of scatterlist.
///
/// Exposes the kernel's [`struct scatterlist`] with `N` entries. It can reference a
/// series of memory buffers, and each buffer will be set by the `set_buf` method.
///
/// The raw mutable pointer of [`RawScatterList`] could be referenced by [`ScatterList`],
/// therefore this struct should be pinned. The recommended way to create such instances
/// is with the [`pin_init`].
///
/// # Examples
///
/// The following is examples of creating [`RawScatterList`] instances.
///
/// ```rust
/// use kernel::stack_pin_init;
/// # use core::pin::Pin;
/// # use crate::scatterlist::RawScatterList;
///
/// const N: usize = 2;
///
/// // Allocates an instance on stack.
/// stack_pin_init!(let foo = RawScatterList::<N>::new());
/// let foo: Pin<&mut RawScatterList<N>> = foo;
///
/// // Alloccate an instance by Box::pin_init.
/// let bar: Pin<Box<RawScatterList<N>>> = Box::pin_init(RawScatterList::<N>::new())?;
///
/// // Set memory buffers.
/// let mut data = [0u8; 1024];
/// let buf = Pin::new(data.as_mut());
/// foo.set_buf(0, buf);
/// # bar.set_buf(0, buf);
/// ```
///
/// [`struct scatterlist`]: ../../../../include/linux/scatterlist.h
#[pin_data]
pub struct RawScatterList<const N: usize> {
    #[pin]
    table: [Opaque<bindings::scatterlist>; N],
    #[pin]
    _p: PhantomPinned,
}

impl<const N: usize> RawScatterList<N> {
    /// Constructs a new initializer.
    pub fn new() -> impl PinInit<Self> {
        build_assert!(N > 0);
        // SAFETY: `slot` is valid while the closure is called. And the scatterlist table
        // will be `N` entries. It's safe to initialize the tabel by `sg_init_table`.
        unsafe {
            init::pin_init_from_closure(move |slot: *mut Self| {
                let ptr = (*slot).table[0].get();
                bindings::sg_init_table(ptr, N as core::ffi::c_uint);
                Ok(())
            })
        }
    }

    /// Set memory buffer for one entry.
    pub fn set_buf(&self, index: usize, entry: Pin<&mut [u8]>) {
        build_assert!(index < N);
        // SAFETY: the `index` is valid and less than the table size. The buffer is
        // pinned and will not be moved.
        unsafe {
            let buf = entry.as_ref().get_ref();
            bindings::sg_set_buf(
                self.table[index].get(),
                buf.as_ptr() as *const core::ffi::c_void,
                buf.len() as core::ffi::c_uint,
            );
        }
    }

    /// Returns an unsafe mutable pointer to the scatterlist table.
    ///
    /// # Safety
    ///
    /// The caller should use some lock to access this pointer safely.
    pub(crate) unsafe fn as_mut_ptr(&self) -> *mut bindings::scatterlist {
        self.table[0].get()
    }
}

/// This struct holds a valid scatterlist pointer.
///
/// The pointer is either constructed by the `new` initializer, or by the `from_raw`
/// method. The differences are that the former owns the scatterlist and its memory
/// buffers could be set by the `copy_from_buffer` method, while the latter only hold
/// a reference to [`RawScatterList`] and its buffers should already be well prepared.
///
/// # Examples
///
/// The following is examples of creating [`ScatterList`] instances.
///
/// ```rust
/// use kernel::{stack_pin_init, stack_try_pin_init};
/// # use core::pin::Pin;
/// # use crate::scatterlist::{RawScatterList, ScatterList};
///
/// let length: usize = 1024;
///
/// // Allocates an instance on stack with `new`.
/// stack_try_pin_init!(let foo = ScatterList::new(length));
/// let foo: Result<Pin<&mut ScatterList>> = foo;
///
/// // Allocates an instance by Box::pin_init with `new`.
/// let bar: Result<Pin<Box<ScatterList>>> = Box::pin_init(ScatterList::new(length));
///
/// // Set memory buffers.
/// let data = [0u8; 1024];
/// foo.unwrap().copy_from_buffer(&data, 0);
/// # bar.unwrap().copy_from_buffer(&data, 0);
///
/// // Creates an instance with `from_raw`.
/// const N: usize = 2;
/// stack_pin_init!(let raw = RawScatterList::<N>::new());
/// let raw: Pin<&mut RawScatterList<N>> = raw;
/// # let mut data = [0u8; 1024];
/// # let buf = Pin::new(data.as_mut());
/// # raw.set_buf(0, buf);
/// stack_pin_init!(let foo = ScatterList::from_raw(raw));
/// let foo: Pin<&mut ScatterList> = foo;
/// ```
#[pin_data(PinnedDrop)]
pub struct ScatterList {
    #[pin]
    lock: Mutex<()>,
    ptr: *mut bindings::scatterlist,
    from_raw: bool,
    length: usize,
}

impl ScatterList {
    /// Constructs a new initializer.
    ///
    /// Returns a type impl [`PinInit<ScatterList>`] or an error with [`ENOMEM`].
    pub fn new(length: usize) -> impl PinInit<Self, Error> {
        try_pin_init!(Self {
            lock <- new_mutex!(()),
            ptr: {
                let mut dummy = 0u32;
                // SAFETY: try to allocate a scatterlist (with `length` in bytes) by calling
                // `sgl_alloc`, which returns a valid pointer to an initialized scatterlist
                // or null pointer upon failure.
                let ptr = unsafe {
                    bindings::sgl_alloc(
                        length as core::ffi::c_ulonglong,
                        bindings::GFP_KERNEL | bindings::__GFP_ZERO,
                        &mut dummy as *mut core::ffi::c_uint,
                    )
                };
                if ptr.is_null() {
                    return Err(ENOMEM);
                }
                ptr
            },
            from_raw: false,
            length,
        })
    }

    /// Constructs from a pinned [`RawScatterList`].
    pub fn from_raw<const N: usize>(ptr: Pin<&mut RawScatterList<N>>) -> impl PinInit<Self> + '_ {
        pin_init!(Self {
            lock <- new_mutex!(()),
            // SAFETY: the `ptr` is valid, and initialized by [`RawScatterList`].
            ptr: unsafe {
                ptr.as_ref().get_ref().as_mut_ptr()
            },
            from_raw: true,
            length: 0,
        })
    }

    /// Returns the length in bytes of the scatterlist.
    ///
    /// If the instance is constructed by `from_raw`, it returns zero.
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns the number of entries in the scatterlist.
    pub fn entries(&self) -> usize {
        // SAFETY: the `ptr` is constructed by `new` or `from_raw`, so it's valid.
        unsafe { bindings::sg_nents(self.ptr) as usize }
    }

    /// Copy from a linear buffer to scatterlist, and skip some bytes from the beginning
    /// of the scatterlist.
    ///
    /// Returns the number of copied bytes, or error with [`EINVAL`] if the skipped bytes
    /// exceed the total length of scattlerlist.
    pub fn copy_from_buffer(&self, buf: &[u8], skip: usize) -> Result<usize> {
        if skip >= self.len() {
            return Err(EINVAL);
        }
        let _lock = self.lock.lock();
        // SAFETY: if the `ptr` is constructed by `from_raw`, the `len` method will return
        // zero, so this method returns `Err(EINVAL)` directly. Also, the skipped bytes are
        // checked above. As a result, `sg_pcopy_from_buffer` gets a safe `ptr` constructed
        // by `new`, and a valid memory buffer.
        let copied = unsafe {
            bindings::sg_pcopy_from_buffer(
                self.ptr,
                self.entries() as core::ffi::c_uint,
                buf.as_ptr() as *const core::ffi::c_void,
                buf.len(),
                skip as bindings::off_t,
            )
        };
        Ok(copied)
    }

    /// Copy form scatterlist to a linear buffer, and skip some bytes from the beginning
    /// of the scatterlist.
    ///
    /// Returns the number of copied bytes, or error with [`EINVAL`] if the skipped bytes
    /// exceed the total length of scattlerlist
    pub fn copy_to_buffer(&self, buf: &mut [u8], skip: usize) -> Result<usize> {
        if skip >= self.len() {
            return Err(EINVAL);
        }
        let _lock = self.lock.lock();
        // SAFETY: if the `ptr` is constructed by `from_raw`, the `len` method will return
        // zero, so this method returns `Err(EINVAL)` directly. Also, the skipped bytes are
        // checked above. As a result, `sg_pcopy_to_buffer` gets a safe `ptr` constructed
        // by `new`, and a valid memory buffer.
        let copied = unsafe {
            bindings::sg_pcopy_to_buffer(
                self.ptr,
                self.entries() as core::ffi::c_uint,
                buf.as_mut_ptr() as *mut core::ffi::c_void,
                buf.len(),
                skip as bindings::off_t,
            )
        };
        Ok(copied)
    }

    /// Returns an unsafe mutable pointer to the scatterlist table.
    ///
    /// # Safety
    ///
    /// The caller should use some lock to access this pointer safely.
    pub(crate) unsafe fn get_mut_ptr(&self) -> *mut bindings::scatterlist {
        self.ptr
    }
}

#[pinned_drop]
impl PinnedDrop for ScatterList {
    fn drop(self: Pin<&mut Self>) {
        if !self.as_ref().get_ref().from_raw {
            // SAFETY: we checked the `ptr` is not construted by `from_raw`,
            // so it is constructed by `new` and is valid.
            unsafe { bindings::sgl_free(self.as_ref().get_ref().ptr) }
        }
    }
}
