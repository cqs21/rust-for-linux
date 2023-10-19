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

    /// Returns a raw pointer to the scatterlist.
    pub unsafe fn as_mut_ptr(&self) -> *mut bindings::scatterlist {
        self.opaque.get()
    }

    /// Obtain a pinned reference to an immutable scatterlist from a raw pointer.
    ///
    /// # Safety
    ///
    /// The `ptr` is null, or pointed to a valid `scatterlist`.
    unsafe fn as_ref(ptr: *mut bindings::scatterlist) -> Option<Pin<&'a Self>> {
        // SAFETY: `sgl` is non-null and valid.
        NonNull::new(ptr).map(|sgl| unsafe { Pin::new_unchecked(&*(sgl.as_ptr() as *const ScatterList<'_>)) })
    }

    /// Obtain a pinned reference to a mutable scatterlist from a raw pointer.
    ///
    /// # Safety
    ///
    /// The `ptr` is null, or pointed to a valid `scatterlist`.
    unsafe fn as_mut(ptr: *mut bindings::scatterlist) -> Option<Pin<&'a mut Self>> {
        // SAFETY: `sgl` is non-null and valid.
        NonNull::new(ptr).map(|sgl| unsafe { Pin::new_unchecked(&mut *(sgl.as_ptr() as *mut ScatterList<'_>)) })
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

/// A [`ScatterList`] table of fixed `N` entries.
///
/// According to the design of kernel's `struct sg_table`, the `page_link`
/// field of one `scatterlist` may contain a pointer to another. That is,
/// there could exist external pointers to it, making it necessary to pin
/// this struct.
///
/// If the table is chainable, the last entry will be reserved for chaining.
/// The recommended way to create such instances is with the [`pin_init`].
///
/// # Examples
///
/// The following are some use cases of [`SgTable<N>`].
///
/// ```rust
/// use core::pin::pin;;
/// # use kernel::error::Result;
/// # use kernel::scatterlist::{ScatterList, SgTable};
///
/// // Prepare memory buffers.
/// let buf0: Pin<&mut [u8]> = pin!([0u8; 512]);
/// let buf1: Pin<&mut [u8]> = pin!([1u8; 512]);
/// let mut entries: Vec<Pin<&mut [u8]>> = Vec::<Pin<&mut [u8]>>::new();
/// entries.try_push(buf0)?;
/// entries.try_push(buf1)?;
///
/// // Allocate an instance on stack.
/// kernel::stack_try_pin_init!(let foo =? SgTable::new(entries.as_slice(), false));
/// let mut foo: Pin<&mut SgTable<'_, 2>> = foo;
/// assert_eq!(foo.count(), 2);
///
/// // Allocate a chainable instance by Box::pin_init.
/// let mut bar: Pin<Box<SgTable<'_, 3>>> = Box::pin_init(SgTable::new(entries.as_slice(), true))?;
/// assert_eq!(bar.count(), 2);
///
/// // Chain two `SgTable` together.
/// bar.chain_sgt(foo.as_mut())?;
/// assert_eq!(bar.count(), 4);
///
/// // Get an immutable reference to the entry in the table.
/// let sgl1: Pin<&ScatterList<'_>> = bar.get(1).ok_or(EINVAL)?;
/// assert_eq!(sgl1.count(), 3);
/// assert_eq!(sgl1.get_buf(), [1u8; 512]);
///
/// // Get a mutable reference to the entry in the table.
/// let sgl2: Pin<&mut ScatterList<'_>> = bar.get_mut(2).ok_or(EINVAL)?;
/// assert_eq!(sgl2.count(), 2);
/// assert_eq!(sgl2.get_buf(), [0u8; 512]);
///
/// // Try to get a non-exist entry from the table.
/// let sgl4 = bar.get(4);
/// assert_eq!(sgl4.is_none(), true);
///
/// // Split the first table from chained scatterlist.
/// bar.split()?;
/// assert_eq!(bar.count(), 2);
/// ```
#[pin_data]
pub struct SgTable<'a, const N: usize> {
    #[pin]
    entries: [ScatterList<'a>; N],
}

impl<'a, const N: usize> SgTable<'a, N> {
    /// Construct a new initializer.
    ///
    /// # Errors
    ///
    /// The length of `entries` should exactly be the available size of [`SgTable<N>`],
    /// or else an error is returned.
    ///
    /// If the table is `chainable`, the available size is `N - 1`, because one entry
    /// should be reserved for chaining.
    pub fn new(
        entries: &'a [Pin<&mut [u8]>],
        chainable: bool,
    ) -> impl PinInit<SgTable<'a, N>, Error> {
        build_assert!(N > 0);
        // SAFETY: `slot` is valid while the closure is called, the `entries` are
        // pinned and valid.
        unsafe {
            init::pin_init_from_closure(move |slot: *mut Self| {
                let mut nr_entry = N;
                if chainable {
                    nr_entry -= 1;
                }
                if nr_entry == 0 || entries.len() != nr_entry {
                    return Err(EINVAL);
                }

                for i in 0..nr_entry {
                    // `slot` contains uninit memory, avoid creating a reference.
                    let opaque = addr_of!((*slot).entries[i].opaque);
                    let sgl = Opaque::raw_get(opaque);

                    bindings::sg_set_buf(sgl, entries[i].as_ptr() as _, entries[i].len() as _);
                    if i + 1 == nr_entry {
                        (*sgl).page_link |= bindings::SG_END as u64;
                        (*sgl).page_link &= !(bindings::SG_CHAIN as u64);
                    }
                }
                Ok(())
            })
        }
    }

    /// Chain two [`SgTable`] together.
    ///
    /// Transfer the last entry of this table as a chainable pointer to the
    /// first entry of `sgt` SgTable.
    ///
    /// # Errors
    ///
    /// Return an error if this table is not chainable or has been chained.
    pub fn chain_sgt<const M: usize>(&mut self, sgt: Pin<&mut SgTable<'_, M>>) -> Result {
        if self.count() != N - 1 {
            return Err(EINVAL);
        }
        self.entries[N - 2].unmark_end();

        // SAFETY: `sgt.entries` are initialized by the `new` constructor,
        // so it's valid.
        let next = unsafe { ScatterList::as_mut(sgt.entries[0].opaque.get()).unwrap() };
        self.entries[N - 1].chain_sgl(next);
        Ok(())
    }

    /// Chain [`SgTable`] and [`ScatterList`] together.
    ///
    /// Transfer the last entry of this table as a chainable pointer to `sgl`
    /// scatterlist.
    ///
    /// # Errors
    ///
    /// Return an error if this table is not chainable or has been chained.
    pub fn chain_sgl(&mut self, sgl: Pin<&mut ScatterList<'_>>) -> Result {
        if self.count() != N - 1 {
            return Err(EINVAL);
        }
        self.entries[N - 2].unmark_end();
        self.entries[N - 1].chain_sgl(sgl);
        Ok(())
    }

    /// Split the first table from chained scatterlist.
    ///
    /// # Errors
    ///
    /// Return an error if this table is not chainable or has not been chained.
    pub fn split(&mut self) -> Result {
        if !self.entries[N - 1].is_chain() {
            return Err(EINVAL);
        }
        self.entries[N - 2].mark_end();
        Ok(())
    }

    /// Return the total count of normal entries in the table.
    ///
    /// It allows to know how many entries are in the table, taking into account
    /// chaining as well.
    pub fn count(&self) -> usize {
        // SAFETY: `self.entries` are initialized by the `new` constructor,
        // so it's valid.
        unsafe { bindings::sg_nents(self.entries[0].opaque.get()) as _ }
    }

    /// Get an immutable reference to `n`th entry in the table.
    ///
    /// Like most indexing operations, the count starts from zero. Return None
    /// if `n` is greater than or equal to the total count of entries.
    pub fn get(&self, n: usize) -> Option<Pin<&ScatterList<'_>>> {
        self.iter().nth(n)
    }

    /// Get a mutable reference to `n`th entry in the table.
    ///
    /// Like most indexing operations, the count starts from zero. Return None
    /// if `n` is greater than or equal to the number of total entries.
    pub fn get_mut(&mut self, n: usize) -> Option<Pin<&mut ScatterList<'_>>> {
        self.iter_mut().nth(n)
    }

    /// Get an iterator for immutable entries.
    pub fn iter(&self) -> Iter<'_> {
        // SAFETY: `self.entries` are initialized by the `new` constructor,
        // so it's valid.
        unsafe { Iter(ScatterList::as_ref(self.entries[0].opaque.get())) }
    }

    /// Get an iterator for mutable entries.
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        // SAFETY: `self.entries` are initialized by the `new` constructor,
        // so it's valid.
        unsafe { IterMut(ScatterList::as_mut(self.entries[0].opaque.get())) }
    }
}

