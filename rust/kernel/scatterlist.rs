// SPDX-License-Identifier: GPL-2.0

//! Scatterlist.
//!
//! C header: [`include/linux/scatterlist.h`](../../../../include/linux/scatterlist.h)

use crate::prelude::*;
use crate::types::Opaque;
use core::marker::PhantomData;
use core::ptr::{addr_of, NonNull};

/// Wrap the kernel's `struct scatterlist`.
///
/// According to the design of kernel's `struct sg_table`, the `page_link`
/// field of one `scatterlist` may contain a pointer to another. That is,
/// there could exist external pointers to it, making it necessary to pin
/// this struct.
///
/// # Invariants
///
/// All instances should be valid, either created by the `new` constructor
/// (see [`pin_init`]), or transmuted from raw pointers (which could be used
/// to reference a valid entry of `sg_table`).
///
/// # Examples
///
/// The following are some use cases of [`ScatterList`].
///
/// ```rust
/// use core::pin::pin;
/// # use kernel::error::Result;
/// # use kernel::scatterlist::ScatterList;
///
/// // Prepare memory buffers.
/// let buf0: Pin<&mut [u8]> = pin!([0u8; 512]);
/// let buf1: Pin<&mut [u8]> = pin!([1u8; 512]);
///
/// // Allocate an instance on stack.
/// kernel::stack_pin_init!(let foo = ScatterList::new(&buf0));
/// let mut foo: Pin<&mut ScatterList<'_>> = foo;
/// assert_eq!(foo.length(), 512);
///
/// // Allocate an instance by Box::pin_init.
/// let bar: Pin<Box<ScatterList<'_>>> = Box::pin_init(ScatterList::new(&buf1))?;
/// assert_eq!(bar.length(), 512);
///
/// // Assert other attributes of an instance.
/// assert_eq!(foo.is_dma_bus_address(), false);
/// assert_eq!(foo.is_chain(), false);
/// assert_eq!(foo.is_last(), true);
/// assert_eq!(foo.count(), 1);
///
/// // Get an immutable reference to memory buffer.
/// assert_eq!(foo.get_buf(), [0u8; 512]);
///
/// // Reset the memory buffer.
/// foo.set_buf(&buf1);
/// assert_eq!(foo.get_buf(), [1u8; 512]);
///
/// // Get a mutable reference to memory buffer.
/// foo.get_mut_buf().fill(2);
/// assert_eq!(foo.get_buf(), [2u8; 512]);
/// ```
#[pin_data]
pub struct ScatterList<'a> {
    #[pin]
    opaque: Opaque<bindings::scatterlist>,
    _p: PhantomData<&'a mut bindings::scatterlist>,
}

impl<'a> ScatterList<'a> {
    /// Construct a new initializer.
    pub fn new(buf: &'a Pin<&mut [u8]>) -> impl PinInit<ScatterList<'a>> {
        // SAFETY: `slot` is valid while the closure is called, the memory
        // buffer is pinned and valid.
        unsafe {
            init::pin_init_from_closure(move |slot: *mut Self| {
                // `slot` contains uninit memory, avoid creating a reference.
                let opaque = addr_of!((*slot).opaque);
                let sgl = Opaque::raw_get(opaque);

                bindings::sg_set_buf(sgl, buf.as_ptr() as _, buf.len() as _);
                (*sgl).page_link |= bindings::SG_END as u64;
                (*sgl).page_link &= !(bindings::SG_CHAIN as u64);
                Ok(())
            })
        }
    }

    /// Obtain a pinned reference to an immutable scatterlist from a raw pointer.
    ///
    /// # Safety
    ///
    /// The `ptr` is null, or pointed to a valid `scatterlist`.
    unsafe fn as_ref(ptr: *mut bindings::scatterlist) -> Option<Pin<&'a Self>> {
        // SAFETY: `sgl` is non-null and valid.
        NonNull::new(ptr).map(|sgl| Pin::new(unsafe { &*(sgl.as_ptr() as *const ScatterList<'_>) }))
    }

    /// Obtain a pinned reference to a mutable scatterlist from a raw pointer.
    ///
    /// # Safety
    ///
    /// The `ptr` is null, or pointed to a valid `scatterlist`.
    unsafe fn as_mut(ptr: *mut bindings::scatterlist) -> Option<Pin<&'a mut Self>> {
        // SAFETY: `sgl` is non-null and valid.
        NonNull::new(ptr)
            .map(|sgl| Pin::new(unsafe { &mut *(sgl.as_ptr() as *mut ScatterList<'_>) }))
    }
}

impl ScatterList<'_> {
    /// Return the offset of memory buffer into the page.
    pub fn offset(&self) -> usize {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe { (*self.opaque.get()).offset as _ }
    }

    /// Return the length of memory buffer.
    pub fn length(&self) -> usize {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe { (*self.opaque.get()).length as _ }
    }

    /// Return the mapped DMA address.
    ///
    /// # Safety
    ///
    /// It is only valid after this scatterlist has been mapped to some bus
    /// address and then called `set_dma` method to setup it.
    pub fn dma_address(&self) -> usize {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe { (*self.opaque.get()).dma_address as _ }
    }

    /// Return the mapped DMA length.
    ///
    /// # Safety
    ///
    /// It is only valid after this scatterlist has been mapped to some bus
    /// address and then called `set_dma` method to setup it.
    pub fn dma_length(&self) -> usize {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        #[cfg(CONFIG_NEED_SG_DMA_LENGTH)]
        unsafe {
            (*self.opaque.get()).dma_length as _
        }
        #[cfg(not(CONFIG_NEED_SG_DMA_LENGTH))]
        unsafe {
            (*self.opaque.get()).length as _
        }
    }

    /// Setup the DMA address and length.
    pub fn set_dma(&mut self, addr: usize, len: usize) {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        #[cfg(CONFIG_NEED_SG_DMA_LENGTH)]
        unsafe {
            (*self.opaque.get()).dma_address = addr as _;
            (*self.opaque.get()).dma_length = len as _;
        }
        #[cfg(not(CONFIG_NEED_SG_DMA_LENGTH))]
        unsafe {
            (*self.opaque.get()).dma_address = addr as _;
            (*self.opaque.get()).length = len as _;
        }
        self.dma_mark_bus_address();
    }

    /// Return `true` if it is mapped with a DMA address.
    pub fn is_dma_bus_address(&self) -> bool {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        #[cfg(CONFIG_PCI_P2PDMA)]
        unsafe {
            ((*self.opaque.get()).dma_flags & bindings::SG_DMA_BUS_ADDRESS) != 0
        }
        #[cfg(not(CONFIG_PCI_P2PDMA))]
        false
    }

    /// Mark it as mapped to a DMA address.
    pub fn dma_mark_bus_address(&mut self) {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        #[cfg(CONFIG_PCI_P2PDMA)]
        unsafe {
            (*self.opaque.get()).dma_flags |= bindings::SG_DMA_BUS_ADDRESS;
        }
    }

    /// Mark it as `not` mapped to a DMA address.
    pub fn dma_unmark_bus_address(&mut self) {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        #[cfg(CONFIG_PCI_P2PDMA)]
        unsafe {
            (*self.opaque.get()).dma_flags &= !bindings::SG_DMA_BUS_ADDRESS;
        }
    }

    /// Return `true` if it is a chainable entry.
    pub fn is_chain(&self) -> bool {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe {
            ((*self.opaque.get()).page_link
                & (bindings::SG_PAGE_LINK_MASK as u64)
                & (bindings::SG_CHAIN as u64))
                != 0
        }
    }

    /// Transfer this scatterlist as a chainable entry, linked to `sgl`.
    pub fn chain_sgl(&mut self, sgl: Pin<&mut ScatterList<'_>>) {
        let addr = sgl.opaque.get() as u64;
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe {
            (*self.opaque.get()).offset = 0;
            (*self.opaque.get()).length = 0;
            (*self.opaque.get()).page_link = addr | (bindings::SG_CHAIN as u64);
        }
        self.unmark_end();
    }

    /// Return `true` if it is the last normal entry in scatterlist.
    pub fn is_last(&self) -> bool {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe {
            ((*self.opaque.get()).page_link
                & (bindings::SG_PAGE_LINK_MASK as u64)
                & (bindings::SG_END as u64))
                != 0
        }
    }

    /// Mark it as the last normal entry in scatterlist.
    pub fn mark_end(&mut self) {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe {
            (*self.opaque.get()).page_link |= bindings::SG_END as u64;
            (*self.opaque.get()).page_link &= !(bindings::SG_CHAIN as u64);
        }
    }

    /// Mark it as `not` the last normal entry in scatterlist.
    pub fn unmark_end(&mut self) {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe {
            (*self.opaque.get()).page_link &= !(bindings::SG_END as u64);
        }
    }

    /// Get an immutable reference to memory buffer.
    pub fn get_buf(&self) -> &[u8] {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        let addr = unsafe { bindings::sg_virt(self.opaque.get()) };
        let len = self.length();
        // SAFETY: `addr` is returned by `sg_virt`, so it is valid. And the memory
        // buffer is set by `new` constructor or `set_buf` method, so it's pinned
        // and valid.
        unsafe { core::slice::from_raw_parts(addr as _, len) }
    }

    /// Get a mutable reference to memory buffer.
    pub fn get_mut_buf(&mut self) -> &mut [u8] {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        let addr = unsafe { bindings::sg_virt(self.opaque.get()) };
        let len = self.length();
        // SAFETY: `addr` is returned by `sg_virt`, so it is valid. And the memory
        // buffer is set by `new` constructor or `set_buf` method, so it's pinned
        // and valid.
        unsafe { core::slice::from_raw_parts_mut(addr as _, len) }
    }

    /// Set the memory buffer.
    pub fn set_buf(&mut self, buf: &Pin<&mut [u8]>) {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        // And `buf` is pinned and valid.
        unsafe {
            bindings::sg_set_buf(
                self.opaque.get(),
                buf.as_ptr() as *const core::ffi::c_void,
                buf.len() as core::ffi::c_uint,
            );
        }
    }

    /// Return the total count of normal entries in scatterlist.
    ///
    /// It allows to know how many entries are in scatterlist, taking into
    /// account chaining as well.
    pub fn count(&self) -> usize {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe { bindings::sg_nents(self.opaque.get()) as _ }
    }

    /// Get an iterator for immutable references.
    pub fn iter(&self) -> Iter<'_> {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe { Iter(ScatterList::as_ref(self.opaque.get())) }
    }

    /// Get an iterator for mutable references.
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        // SAFETY: By the type invariant, we know that `self.opaque` is valid.
        unsafe { IterMut(ScatterList::as_mut(self.opaque.get())) }
    }
}

/// An iterator that yields [`Pin<&ScatterList>`].
///
/// Only iterate normal scatterlist entries, chainable entry will be skipped.
pub struct Iter<'a>(Option<Pin<&'a ScatterList<'a>>>);

impl<'a> Iterator for Iter<'a> {
    type Item = Pin<&'a ScatterList<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ptr = match &self.0 {
            None => return None,
            Some(sgl) => sgl.opaque.get(),
        };
        // SAFETY: `ptr` is from `self.opaque`, it is valid by the type invariant.
        // And `next` is null, or the next valid scatterlist entry.
        unsafe {
            let next = bindings::sg_next(ptr);
            self.0 = ScatterList::as_ref(next);
            ScatterList::as_ref(ptr)
        }
    }
}

/// An iterator that yields [`Pin<&mut ScatterList>`].
///
/// Only iterate normal scatterlist entries, chainable entry will be skipped.
pub struct IterMut<'a>(Option<Pin<&'a mut ScatterList<'a>>>);

impl<'a> Iterator for IterMut<'a> {
    type Item = Pin<&'a mut ScatterList<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ptr = match &self.0 {
            None => return None,
            Some(sgl) => sgl.opaque.get(),
        };
        // SAFETY: `ptr` is from `self.opaque`, it is valid by the type invariant.
        // And `next` is null, or the next valid scatterlist entry.
        unsafe {
            let next = bindings::sg_next(ptr);
            self.0 = ScatterList::as_mut(next);
            ScatterList::as_mut(ptr)
        }
    }
}
