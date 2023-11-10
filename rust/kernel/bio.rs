use bindings::{GFP_KERNEL, PAGE_SHIFT};
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use kernel::error::to_result;
use kernel::prelude::*;
use kernel::types::Opaque;

pub const GFP_NOIO: bindings::gfp_t =
    bindings::___GFP_DIRECT_RECLAIM | bindings::___GFP_KSWAPD_RECLAIM;

const BIO_INLINE_VECS: core::ffi::c_ushort = 4;

const BLOCK_SIZE: usize = 1 << PAGE_SHIFT;

/// A Rust wrapper for `struct block_device`
pub struct BlockDevice {
    opaque: Opaque<bindings::block_device>,
}

impl BlockDevice {
    pub unsafe fn borrow<'a>(ptr: *const bindings::block_device) -> &'a Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &*(ptr as *const Self) }
    }

    pub unsafe fn borrow_mut<'a>(ptr: *mut bindings::block_device) -> &'a mut Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &mut *(ptr as *mut Self) }
    }
}

/// A Rust wrapper for `struct bio`
pub struct Bio {
    inner: NonNull<bindings::bio>,
    with_owned_pages: bool,
    nr_pages: usize,
}

impl Bio {
    pub unsafe fn from_raw(ptr: *mut bindings::bio) -> Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe {
            // Get a reference to a bio, so it won't disappear.
            bindings::bio_get(ptr);
            Self {
                inner: NonNull::new_unchecked(ptr),
                with_owned_pages: false,
                nr_pages: 0,
            }
        }
    }

    /// Create a bio with nr_blocks as io buffer.
    pub fn create(bdev: &BlockDevice, nr_blocks: usize, opf: u32) -> Result<Self> {
        let bio = unsafe {
            bindings::bio_alloc_bioset(
                bdev.opaque.get(),
                BIO_INLINE_VECS,
                opf,
                GFP_NOIO,
                &mut bindings::fs_bio_set,
            )
        };
        if bio.is_null() {
            return Err(ENOMEM);
        }

        let virt = unsafe { bindings::alloc_pages_exact(nr_blocks * BLOCK_SIZE, GFP_KERNEL) };
        if virt.is_null() {
            unsafe {
                bindings::bio_put(bio);
            }
            return Err(ENOMEM);
        }

        unsafe {
            let page = bindings::virt_to_page(virt);
            bindings::__bio_add_page(bio, page, (nr_blocks * BLOCK_SIZE) as _, 0);
            Ok(Self {
                inner: NonNull::new_unchecked(bio),
                with_owned_pages: true,
                nr_pages: nr_blocks,
            })
        }
    }

    // Clone a bio that shares the original bio's biovec.
    pub fn alloc_clone(&self) -> Result<Self> {
        let src = self.inner.as_ptr();
        let cloned = unsafe {
            bindings::bio_alloc_clone((*src).bi_bdev, src, GFP_NOIO, &mut bindings::fs_bio_set)
        };
        if cloned.is_null() {
            return Err(ENOMEM);
        }

        unsafe {
            Ok(Self {
                inner: NonNull::new_unchecked(cloned),
                with_owned_pages: false,
                nr_pages: 0,
            })
        }
    }

    /// Split a smaller bio from current bio.
    pub fn split(&self, sectors: usize) -> Result<Self> {
        let bio = self.inner.as_ptr();
        let split = unsafe {
            bindings::bio_split(
                bio,
                sectors as core::ffi::c_int,
                GFP_NOIO,
                &mut bindings::fs_bio_set,
            )
        };
        if split.is_null() {
            return Err(EINVAL);
        }

        unsafe {
            Ok(Self {
                inner: NonNull::new_unchecked(split),
                with_owned_pages: false,
                nr_pages: 0,
            })
        }
    }

    /// Get the operation and flags. The bottom 8 bits are encoding the operation,
    /// and the remaining 24 for flags.
    pub fn opf(&self) -> u32 {
        unsafe { (*self.inner.as_ptr()).bi_opf }
    }

    /// Set the operation and flags.
    pub fn set_opf(&mut self, opf: u32) {
        unsafe { (*self.inner.as_ptr()).bi_opf = opf }
    }

    /// Return `true` if the bio request is write.
    pub fn is_write(&self) -> bool {
        self.opf() & bindings::req_op_REQ_OP_WRITE != 0
    }

    /// Return the start sector of bio.
    pub fn sector(&self) -> usize {
        unsafe { (*self.inner.as_ptr()).bi_iter.bi_sector as _ }
    }

    /// Set the start sector of bio.
    pub fn set_sector(&mut self, sector: usize) {
        unsafe { (*self.inner.as_ptr()).bi_iter.bi_sector = sector as _ }
    }

    /// Get the size of bio.
    pub fn size(&self) -> usize {
        unsafe { (*self.inner.as_ptr()).bi_iter.bi_size as _ }
    }

    /// Set the size of bio.
    pub fn set_size(&mut self, size: usize) {
        unsafe { (*self.inner.as_ptr()).bi_iter.bi_size = size as _ }
    }

    /// Set the block device of bio.
    pub fn set_dev(&mut self, bdev: &BlockDevice) {
        unsafe { bindings::bio_set_dev(self.inner.as_ptr(), bdev.opaque.get()) }
    }

    /// Submit the bio.
    ///
    /// The success/failure status of the request, along with notification of
    /// completion, is delivered asynchronously through the `bi_end_io` callback
    /// in bio.
    pub fn submit(&self) {
        unsafe { bindings::submit_bio(self.inner.as_ptr()) }
    }

    /// Submit a bio, and wait until it completes.
    pub fn submit_and_wait(&self) -> Result<()> {
        let err = unsafe { bindings::submit_bio_wait(self.inner.as_ptr()) };
        to_result(err)
    }

    /// End the bio.
    ///
    /// This will end I/O on the whole bio. No one should call bi_end_io()
    /// directly on a bio unless they own it and thus know that it has an
    /// end_io function.
    pub fn end(&self) {
        unsafe { bindings::bio_endio(self.inner.as_ptr()) }
    }

    /// Return a iterator on the bio_vec.
    pub fn vec_iter(&self) -> BioVecIter {
        let bio = self.inner.as_ptr();
        unsafe { BioVecIter::from_raw((*bio).bi_io_vec, (*bio).bi_vcnt as _) }
    }
}

impl Drop for Bio {
    fn drop(&mut self) {
        let bio = self.inner.as_ptr();
        if self.with_owned_pages {
            unsafe {
                let page = (*(*bio).bi_io_vec).bv_page;
                let virt = bindings::page_to_virt(page);
                bindings::free_pages_exact(virt, self.nr_pages * BLOCK_SIZE);
            }
        }
        unsafe {
            // Put a reference to a &struct bio, either one you have gotten
            // with `bio_alloc`, `bio_get` or `bio_clone_*`. The last put of
            // a bio will free it.
            bindings::bio_put(bio);
        }
    }
}

pub struct BioVec {
    ptr: NonNull<bindings::bio_vec>,
    virt_addr: usize,
    len: usize,
}

impl BioVec {
    pub unsafe fn from_raw(bio_vec: *mut bindings::bio_vec) -> Self {
        unsafe {
            let mut ptr = bindings::kmap_local_page((*bio_vec).bv_page);
            let virt_addr = ptr.add((*bio_vec).bv_offset as _) as usize;
            Self {
                ptr: NonNull::new_unchecked(bio_vec),
                virt_addr,
                len: (*bio_vec).bv_len as usize,
            }
        }
    }
}

impl Drop for BioVec {
    fn drop(&mut self) {
        unsafe { bindings::kunmap_local(self.virt_addr as _) }
    }
}

impl Deref for BioVec {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        unsafe { core::slice::from_raw_parts(self.virt_addr as _, self.len) }
    }
}

impl DerefMut for BioVec {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { core::slice::from_raw_parts_mut(self.virt_addr as _, self.len) }
    }
}

pub struct BioVecIter {
    bio_vec: NonNull<bindings::bio_vec>,
    bi_vcnt: usize,
}

impl BioVecIter {
    pub unsafe fn from_raw(bio_vec: *mut bindings::bio_vec, bi_vcnt: usize) -> Self {
        unsafe {
            Self {
                bio_vec: NonNull::new_unchecked(bio_vec),
                bi_vcnt,
            }
        }
    }
}

impl Iterator for BioVecIter {
    type Item = BioVec;

    fn next(&mut self) -> Option<Self::Item> {
        if self.bi_vcnt == 0 {
            return None;
        }
        let next = unsafe { self.bio_vec.as_ptr().add(1) };
        let vcnt = self.bi_vcnt - 1;
        unsafe {
            let bio_vec = BioVec::from_raw(next);
            self.bio_vec = NonNull::new_unchecked(next);
            self.bi_vcnt = vcnt;
            Some(bio_vec)
        }
    }
}
