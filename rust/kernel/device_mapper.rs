// SPDX-License-Identifier: GPL-2.0

//! Device Mapper.
//!
//! C header: [`include/linux/device-mapper.h`](../../../../include/linux/device-mapper.h)

use core::marker::PhantomData;
use core::ops::{Index, Range};
use core::ptr::{addr_of, NonNull};

use crate::error::to_result;
use crate::prelude::*;
use crate::str::{CStr, CString};
use crate::types::Opaque;

/// Declare operations that a device mapper target can do.
#[vtable]
pub trait TargetOperations: Sized {
    /// Persist user data.
    type Private: Sync;

    /// Constructor. The target will already have the table, type, begin and
    /// len fields filled in. A `Private` struct can be returned to persist
    /// its own context.
    fn ctr(t: &mut Target<Self>, args: Args) -> Result<Box<Self::Private>>;

    /// Destructor. The target could clean up anything hidden in `Private`,
    /// and `Private` itself can be dropped automatically.
    fn dtr(t: &mut Target<Self>);

    /// Map block IOs. Return [`MapState`] to indicate how to handle the `bio`
    /// later (end or resubmit).
    fn map(t: &mut Target<Self>, bio: Pin<&mut Bio>) -> MapState;

    /// Map `request`. Return [`MapState`] and the optional cloned `request`.
    #[allow(unused)]
    fn clone_and_map_rq<'a>(
        t: &mut Target<Self>,
        rq: Pin<&mut Request>,
        map_ctx: &mut MapInfo,
    ) -> (MapState, Option<Pin<&'a mut Request>>) {
        unimplemented!()
    }

    /// Release the cloned `request`.
    #[allow(unused)]
    fn release_clone_rq(rq: Pin<&mut Request>, map_ctx: &mut MapInfo) {
        unimplemented!()
    }

    /// End the `bio`. Return [`EndState`] and [`BlkStatus`].
    #[allow(unused)]
    fn end_io(t: &mut Target<Self>, bio: Pin<&mut Bio>) -> (EndState, BlkStatus) {
        unimplemented!()
    }

    /// End the `request`. Return [`EndState`].
    #[allow(unused)]
    fn rq_end_io(
        t: &mut Target<Self>,
        rq: Pin<&mut Request>,
        map_ctx: &mut MapInfo,
        err: BlkStatus,
    ) -> EndState {
        unimplemented!()
    }

    /// Hook presuspend.
    #[allow(unused)]
    fn presuspend(t: &mut Target<Self>) {
        unimplemented!()
    }

    /// Hook presuspend_undo.
    #[allow(unused)]
    fn presuspend_undo(t: &mut Target<Self>) {
        unimplemented!()
    }

    /// Hook postsuspend.
    #[allow(unused)]
    fn postsuspend(t: &mut Target<Self>) {
        unimplemented!()
    }

    /// Hook preresume.
    #[allow(unused)]
    fn preresume(t: &mut Target<Self>) -> Result {
        unimplemented!()
    }

    /// Hook resume.
    #[allow(unused)]
    fn resume(t: &mut Target<Self>) {
        unimplemented!()
    }

    /// Check if target is busy.
    #[allow(unused)]
    fn busy(t: &mut Target<Self>) -> bool {
        unimplemented!()
    }

    /// Return the target status.
    #[allow(unused)]
    fn status(t: &mut Target<Self>, type_: StatusType, flags: StatusFlags) -> Option<CString> {
        unimplemented!()
    }

    /// Handle messages to the target.
    #[allow(unused)]
    fn message(t: &mut Target<Self>, args: Args) -> Result<CString> {
        unimplemented!()
    }

    /// Propagate report zones command to underlying devices.
    #[allow(unused)]
    fn report_zones(t: &mut Target<Self>, args: &mut [ReportZonesArgs]) -> Result {
        unimplemented!()
    }

    /// Pass on ioctl to the underlying device.
    #[allow(unused)]
    fn prepare_ioctl(t: &mut Target<Self>) -> (i32, Option<NonNull<TargetDevice<Self>>>) {
        unimplemented!()
    }

    /// Iterate the underlying devices.
    #[allow(unused)]
    fn iterate_devices(t: &mut Target<Self>) -> Result<Box<dyn Iterator<Item = IterDevice<Self>>>> {
        unimplemented!()
    }

    /// Setup target request queue limits.
    #[allow(unused)]
    fn io_hints(t: &mut Target<Self>, limits: &mut QueueLimits) {
        unimplemented!()
    }

    /// Translate a device-relative logical-page-offset into an
    /// absolute physical pfn.
    ///
    /// Return the `addr` and the `pages` available for `DAX` at
    /// that pfn, if success.
    #[allow(unused)]
    fn direct_access(
        t: &mut Target<Self>,
        pgoff: usize,
        nr_pages: usize,
        mode: DaxMode,
    ) -> Result<(usize, Range<usize>)> {
        unimplemented!()
    }

    /// Zero page range.
    #[allow(unused)]
    fn dax_zero_page_range(t: &mut Target<Self>, pgoff: usize, nr_pages: usize) -> Result {
        unimplemented!()
    }

    /// Recover a poisoned range by DAX device driver capable of
    /// clearing poison.
    #[allow(unused)]
    fn dax_recovery_write(
        t: &mut Target<Self>,
        iov_iter: Pin<&mut IovIter>,
        pgoff: usize,
        region: Range<usize>,
    ) -> usize {
        unimplemented!()
    }
}

/// Wrap the kernel struct `target_type`.
///
/// It contains a struct `list_head` for internal device-mapper use, so it
/// should be pinned. Users can use this struct to register/unregister their
/// own device mapper target.
#[pin_data(PinnedDrop)]
pub struct TargetType {
    #[pin]
    opaque: Opaque<bindings::target_type>,
}

/// Define target feature type.
pub type Feature = u64;

// SAFETY: It's OK to access `TargetType` from multiple threads. The
// `dm_register_target` and `dm_unregister_target` provides its own
// synchronization.
unsafe impl Sync for TargetType {}

macro_rules! check_target_operations {
    ($tt:expr, $(($op:ident, $filed:ident, $func:ident),)+) => {$(
        if <T as TargetOperations>::$op {
            (*$tt).$filed = Some(TargetType::$func::<T>);
        }
    )+};
}

impl TargetType {
    /// Provide an in-place constructor to register a new device mapper target.
    pub fn register<T: TargetOperations>(
        module: &'static ThisModule,
        name: &'static CStr,
        version: [u32; 3],
        feature: Feature,
    ) -> impl PinInit<Self, Error> {
        // SAFETY: `slot` is valid while the closure is called.
        unsafe {
            init::pin_init_from_closure(move |slot: *mut Self| {
                // `slot` contains uninit memory, avoid creating a reference.
                let opaque = addr_of!((*slot).opaque);
                let tt = Opaque::raw_get(opaque);

                (*tt).module = module.0;
                (*tt).name = name.as_char_ptr();
                (*tt).version = version;
                (*tt).features = feature;

                check_target_operations!(
                    tt,
                    (HAS_CTR, ctr, dm_ctr_fn),
                    (HAS_DTR, dtr, dm_dtr_fn),
                    (HAS_MAP, map, dm_map_fn),
                    (
                        HAS_CLONE_AND_MAP_RQ,
                        clone_and_map_rq,
                        dm_clone_and_map_request_fn
                    ),
                    (
                        HAS_RELEASE_CLONE_RQ,
                        release_clone_rq,
                        dm_release_clone_request_fn
                    ),
                    (HAS_END_IO, end_io, dm_endio_fn),
                    (HAS_RQ_END_IO, rq_end_io, dm_request_endio_fn),
                    (HAS_PRESUSPEND, presuspend, dm_presuspend_fn),
                    (HAS_PRESUSPEND_UNDO, presuspend_undo, dm_presuspend_undo_fn),
                    (HAS_POSTSUSPEND, postsuspend, dm_postsuspend_fn),
                    (HAS_PRERESUME, preresume, dm_preresume_fn),
                    (HAS_RESUME, resume, dm_resume_fn),
                    (HAS_BUSY, busy, dm_busy_fn),
                    (HAS_STATUS, status, dm_status_fn),
                    (HAS_MESSAGE, message, dm_message_fn),
                    (HAS_REPORT_ZONES, report_zones, dm_report_zones_fn),
                    (HAS_PREPARE_IOCTL, prepare_ioctl, dm_prepare_ioctl_fn),
                    (HAS_ITERATE_DEVICES, iterate_devices, dm_iterate_devices_fn),
                    (HAS_IO_HINTS, io_hints, dm_io_hints_fn),
                    (HAS_DIRECT_ACCESS, direct_access, dm_dax_direct_access_fn),
                    (
                        HAS_DAX_ZERO_PAGE_RANGE,
                        dax_zero_page_range,
                        dm_dax_zero_page_range_fn
                    ),
                    (
                        HAS_DAX_RECOVERY_WRITE,
                        dax_recovery_write,
                        dm_dax_recovery_write_fn
                    ),
                );

                to_result(bindings::dm_register_target(tt))
            })
        }
    }
}

#[pinned_drop]
impl PinnedDrop for TargetType {
    fn drop(self: Pin<&mut Self>) {
        // SAFETY: `self.opaque` are initialized by the `register` constructor,
        // so it's valid.
        unsafe {
            bindings::dm_unregister_target(self.opaque.get());
        }
    }
}

impl TargetType {
    unsafe extern "C" fn dm_ctr_fn<T: TargetOperations>(
        target: *mut bindings::dm_target,
        argc: core::ffi::c_uint,
        argv: *mut *mut core::ffi::c_char,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel splits arguments by `dm_split_args`, then pass
        // suitable `argc` and `argv` to `dm_ctr_fn`. If `argc` is not zero,
        // `argv` is non-null and valid.
        let args = unsafe { Args::new(argc, argv) };

        // SAFETY: the kernel should pass a valid `dm_target`.
        let t = unsafe { Target::borrow_mut(target) };
        T::ctr(t, args).map_or_else(
            |e| e.to_errno(),
            // SAFETY: the kernel should pass a valid `dm_target`.
            |p| unsafe {
                (*target).private = Box::into_raw(p) as _;
                0
            },
        )
    }
    unsafe extern "C" fn dm_dtr_fn<T: TargetOperations>(ti: *mut bindings::dm_target) {
        // SAFETY: the kernel should pass a valid `dm_target`.
        let t = unsafe { Target::borrow_mut(ti) };
        T::dtr(t);
        // SAFETY: `private` is constructed in `dm_ctr_fn`, and we drop it here.
        unsafe {
            let ptr = (*ti).private as *mut T::Private;
            drop(Box::from_raw(ptr));
            (*ti).private = core::ptr::null_mut();
        }
    }
    unsafe extern "C" fn dm_map_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        bio: *mut bindings::bio,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass a valid `dm_target` and `bio`.
        unsafe {
            let t = Target::borrow_mut(ti);
            let bio = Bio::from_raw(bio);
            T::map(t, bio) as _
        }
    }
    unsafe extern "C" fn dm_clone_and_map_request_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        rq: *mut bindings::request,
        map_context: *mut bindings::map_info,
        clone: *mut *mut bindings::request,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target`, `request`
        // and `map_info` pointers.
        unsafe {
            let t = Target::borrow_mut(ti);
            let rq = Request::from_raw(rq);
            let map_ctx = MapInfo::borrow_mut(map_context);
            let (map_state, rq_cloned) = T::clone_and_map_rq(t, rq, map_ctx);
            *clone = rq_cloned.map_or(core::ptr::null_mut(), |rq| rq.opaque.get());
            map_state as _
        }
    }
    unsafe extern "C" fn dm_release_clone_request_fn<T: TargetOperations>(
        clone: *mut bindings::request,
        map_context: *mut bindings::map_info,
    ) {
        // SAFETY: the kernel should pass valid `request` and `map_info` pointers.
        unsafe {
            let rq = Request::from_raw(clone);
            let map_ctx = MapInfo::borrow_mut(map_context);
            T::release_clone_rq(rq, map_ctx);
        }
    }
    unsafe extern "C" fn dm_endio_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        bio: *mut bindings::bio,
        error: *mut bindings::blk_status_t,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target`, `bio` and
        // `error` pointers.
        unsafe {
            let t = Target::borrow_mut(ti);
            let bio = Bio::from_raw(bio);
            let (end_state, blk_status) = T::end_io(t, bio);
            *error = blk_status as _;
            end_state as _
        }
    }
    unsafe extern "C" fn dm_request_endio_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        clone: *mut bindings::request,
        error: bindings::blk_status_t,
        map_context: *mut bindings::map_info,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target`, `request`
        // and `map_info` pointers.
        unsafe {
            let t = Target::borrow_mut(ti);
            let rq = Request::from_raw(clone);
            let map_ctx = MapInfo::borrow_mut(map_context);
            T::rq_end_io(t, rq, map_ctx, (error as u32).into()) as _
        }
    }
    unsafe extern "C" fn dm_presuspend_fn<T: TargetOperations>(ti: *mut bindings::dm_target) {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::presuspend(t);
    }
    unsafe extern "C" fn dm_presuspend_undo_fn<T: TargetOperations>(ti: *mut bindings::dm_target) {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::presuspend_undo(t);
    }
    unsafe extern "C" fn dm_postsuspend_fn<T: TargetOperations>(ti: *mut bindings::dm_target) {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::postsuspend(t);
    }
    unsafe extern "C" fn dm_preresume_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::preresume(t).map_or_else(|e| e.to_errno(), |_| 0)
    }
    unsafe extern "C" fn dm_resume_fn<T: TargetOperations>(ti: *mut bindings::dm_target) {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::resume(t);
    }
    unsafe extern "C" fn dm_busy_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::busy(t) as _
    }
    unsafe extern "C" fn dm_status_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        status_type: bindings::status_type_t,
        status_flags: core::ffi::c_uint,
        result: *mut core::ffi::c_char,
        maxlen: core::ffi::c_uint,
    ) {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        if let Some(s) = T::status(t, status_type.into(), status_flags.into()) {
            let count = s.len_with_nul().min(maxlen as _);
            // SAFETY: the kernel should pass valid `result` pointer, and
            // `count` is not greater than `maxlen`.
            unsafe {
                core::ptr::copy(s.as_char_ptr(), result, count);
            }
        }
    }
    unsafe extern "C" fn dm_message_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        argc: core::ffi::c_uint,
        argv: *mut *mut core::ffi::c_char,
        result: *mut core::ffi::c_char,
        maxlen: core::ffi::c_uint,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel splits arguments by `dm_split_args`, then pass
        // suitable `argc` and `argv` to `dm_ctr_fn`. If `argc` is not zero,
        // `argv` is non-null and valid.
        let args = unsafe { Args::new(argc, argv) };

        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        T::message(t, args).map_or_else(
            |e| e.to_errno(),
            // SAFETY: the kernel should pass valid `result` pointer, and
            // `count` is not greater than `maxlen`.
            |ret| unsafe {
                let count = ret.len_with_nul().min(maxlen as _);
                core::ptr::copy(ret.as_char_ptr(), result, count);
                0
            },
        )
    }
    unsafe extern "C" fn dm_report_zones_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        args: *mut bindings::dm_report_zones_args,
        nr_zones: core::ffi::c_uint,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };

        let args = if nr_zones > 0 {
            // SAFETY: the kernel should pass valid `args`, if `nr_zones`
            // is not zero.
            unsafe {
                let first = ReportZonesArgs::borrow_mut(args);
                core::slice::from_raw_parts_mut(first as _, nr_zones as _)
            }
        } else {
            &mut []
        };
        T::report_zones(t, args).map_or_else(|e| e.to_errno(), |_| 0)
    }
    unsafe extern "C" fn dm_prepare_ioctl_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        bdev: *mut *mut bindings::block_device,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };

        match T::prepare_ioctl(t) {
            (err, None) => err,
            // SAFETY: `td` and `dev` is `NonNull`, both of them are valid.
            (ret, Some(td)) => unsafe {
                let dm_dev = td.as_ref().dev.as_ptr();
                let block_dev = (*dm_dev).bdev;
                *bdev = block_dev;
                ret
            },
        }
    }
    unsafe extern "C" fn dm_iterate_devices_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        fn_: bindings::iterate_devices_callout_fn,
        data: *mut core::ffi::c_void,
    ) -> core::ffi::c_int {
        let Some(fn_) = fn_ else {
            pr_warn!("Invalid iterate_devices_callout_fn, skipped!");
            return 0;
        };

        // SAFETY: the kernel should pass valid `dm_target` pointer.
        let t = unsafe { Target::borrow_mut(ti) };
        let devices = match T::iterate_devices(t) {
            Err(e) => return e.to_errno(),
            Ok(devices) => devices,
        };

        let mut ret = 0;
        for (target_device, start, len) in devices {
            // SAFETY: `target_device` is `NonNull`, it is also valid.
            // `fn_` is checked above, it is non-null, and the kernel
            // should pass valid `iterate_devices_callout_fn`.
            unsafe {
                let dev = target_device.as_ref().dev.as_ptr();
                ret = fn_(ti, dev, start as _, len as _, data);
                if ret != 0 {
                    break;
                }
            }
        }
        ret
    }
    unsafe extern "C" fn dm_io_hints_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        limits: *mut bindings::queue_limits,
    ) {
        // SAFETY: the kernel should pass valid `dm_target` and `queue_limits`
        // pointers.
        unsafe {
            let t = Target::borrow_mut(ti);
            let limits = QueueLimits::borrow_mut(limits);
            T::io_hints(t, limits);
        }
    }
    unsafe extern "C" fn dm_dax_direct_access_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        pgoff: core::ffi::c_ulong,
        nr_pages: core::ffi::c_long,
        mode: bindings::dax_access_mode,
        kaddr: *mut *mut core::ffi::c_void,
        pfn: *mut bindings::pfn_t,
    ) -> core::ffi::c_long {
        // SAFETY: the kernel should pass valid `dm_target`, `kaddr` and
        // `pfn` pointers.
        unsafe {
            let t = Target::borrow_mut(ti);
            match T::direct_access(t, pgoff as _, nr_pages as _, mode.into()) {
                Ok((addr, pages)) => {
                    *kaddr = addr as _;
                    (*pfn).val = pages.start as _;
                    pages.len() as _
                }
                Err(e) => e.to_errno() as _,
            }
        }
    }
    unsafe extern "C" fn dm_dax_zero_page_range_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        pgoff: core::ffi::c_ulong,
        nr_pages: usize,
    ) -> core::ffi::c_int {
        // SAFETY: the kernel should pass valid `dm_target` pointer.
        unsafe {
            let t = Target::borrow_mut(ti);
            T::dax_zero_page_range(t, pgoff as _, nr_pages as _)
                .map_or_else(|e| e.to_errno(), |_| 0)
        }
    }
    unsafe extern "C" fn dm_dax_recovery_write_fn<T: TargetOperations>(
        ti: *mut bindings::dm_target,
        pgoff: core::ffi::c_ulong,
        addr: *mut core::ffi::c_void,
        bytes: usize,
        i: *mut bindings::iov_iter,
    ) -> usize {
        let region = Range {
            start: addr as usize,
            end: (addr as usize) + bytes,
        };

        // SAFETY: the kernel should pass valid `dm_target` and `iov_iter`
        // pointers.
        unsafe {
            let t = Target::borrow_mut(ti);
            let iov_iter = IovIter::from_raw(i);
            T::dax_recovery_write(t, iov_iter, pgoff as _, region)
        }
    }
}

/// Wrap the kernel struct `dm_target`.
///
/// This struct represents a device mapper target. And the device mapper
/// core will alloc/free `dm_target` instances, so we just `borrow` it.
/// It also holds a `Private` struct, which is used to persist user's data,
/// and can be accessed by the `private` method.
pub struct Target<T: TargetOperations + Sized> {
    opaque: Opaque<bindings::dm_target>,
    _p: PhantomData<*mut T::Private>,
}

impl<T: TargetOperations> Target<T> {
    unsafe fn borrow<'a>(ptr: *const bindings::dm_target) -> &'a Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &*(ptr as *const Self) }
    }

    unsafe fn borrow_mut<'a>(ptr: *mut bindings::dm_target) -> &'a mut Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &mut *(ptr as *mut Self) }
    }

    /// Access user's private data.
    pub fn private(&mut self) -> Option<Pin<&mut T::Private>> {
        let t = self.opaque.get();
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        // And 'p' is non-null and assigned in `dm_ctr_fn`, so it's valid.
        unsafe {
            ((*t).private as *mut T::Private)
                .as_mut()
                .map(|p| Pin::new_unchecked(p))
        }
    }

    /// Return the target name.
    pub fn name(&self) -> &CStr {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            let name = (*(*self.opaque.get()).type_).name;
            CStr::from_char_ptr(name)
        }
    }

    /// Return the target version.
    pub fn version(&self) -> [u32; 3] {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*(*self.opaque.get()).type_).version }
    }

    /// Return the target begin sector.
    pub fn begin_sector(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).begin as _ }
    }

    /// Return the target total sectors.
    pub fn total_sectors(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).len as _ }
    }

    /// Get the underlying device by `path`. The `dm_put_device` will be called when
    /// [`TargetDevice`] is dropped.
    pub fn get_device(&mut self, path: &CStr) -> Result<TargetDevice<T>> {
        let mut dd = core::ptr::null_mut();
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            let mode = bindings::dm_table_get_mode((*self.opaque.get()).table);
            match bindings::dm_get_device(self.opaque.get(), path.as_char_ptr(), mode, &mut dd) {
                0 => {
                    let ti = self.opaque.get();
                    Ok(TargetDevice::from_raw(ti, dd))
                }
                err => Err(Error::from_errno(err)),
            }
        }
    }

    /// Return maximum size (in sectors) of I/O submitted to the target.
    pub fn max_io_len(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).max_io_len as _ }
    }

    /// Set maximum size (in sectors) of I/O submitted to the target.
    pub fn set_max_io_len(&mut self, len: usize) -> Result {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            to_result(bindings::dm_set_target_max_io_len(
                self.opaque.get(),
                len as _,
            ))
        }
    }

    /// Return the number of zero-length barrier bios that will be submitted
    /// to the target for the purpose of flushing cache.
    pub fn num_flush_bios(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).num_flush_bios as _ }
    }

    /// Set the number of zero-length barrier bios that will be submitted
    /// to the target for the purpose of flushing cache.
    pub fn set_num_flush_bios(&mut self, num: usize) {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            (*self.opaque.get()).num_flush_bios = num as _;
        }
    }

    /// Return the number of discard bios.
    pub fn num_discard_bios(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).num_discard_bios as _ }
    }

    /// Set the number of discard bios.
    pub fn set_num_discard_bios(&mut self, num: usize) {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            (*self.opaque.get()).num_discard_bios = num as _;
        }
    }

    /// Return the number of secure erase bios.
    pub fn num_secure_erase_bios(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).num_secure_erase_bios as _ }
    }

    /// Set the number of secure erase bios.
    pub fn set_num_secure_erase_bios(&mut self, num: usize) {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            (*self.opaque.get()).num_secure_erase_bios = num as _;
        }
    }

    /// Return the number of WRITE ZEROES bios.
    pub fn num_write_zeroes_bios(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).num_write_zeroes_bios as _ }
    }

    /// Set the number of WRITE ZEROES bios.
    pub fn set_num_write_zeroes_bios(&mut self, num: usize) {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            (*self.opaque.get()).num_write_zeroes_bios = num as _;
        }
    }

    /// Return the minimum number of extra bytes allocated in each io
    /// for the target to use.
    pub fn per_io_data_size(&self) -> usize {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { (*self.opaque.get()).per_io_data_size as _ }
    }

    /// Set the minimum number of extra bytes allocated in each io
    /// for the target to use.
    pub fn set_per_io_data_size(&mut self, size: usize) {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            (*self.opaque.get()).per_io_data_size = size as _;
        }
    }

    /// Set an error string for the target, could be used
    /// by [`TargetOperations::ctr`].
    pub fn set_error(&mut self, err: &CStr) {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe {
            (*self.opaque.get()).error = err.as_char_ptr() as _;
        }
    }

    /// Check if the target is suspended.
    pub fn suspended(&self) -> bool {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { bindings::dm_suspended(self.opaque.get()) != 0 }
    }

    /// Check if the target is post_suspending.
    pub fn post_suspending(&self) -> bool {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { bindings::dm_post_suspending(self.opaque.get()) != 0 }
    }

    /// Check if the target is noflush_suspending.
    pub fn noflush_suspending(&self) -> bool {
        // SAFETY: `self.opaque` is borrowed from foreign pointer, should be valid.
        unsafe { bindings::dm_noflush_suspending(self.opaque.get()) != 0 }
    }
}

/// Represent an underlying device of a device mapper target.
///
/// We also holds a pointer to `dm_target`, so that we can call
/// `dm_put_device` in `drop`, to close the device correctly.
pub struct TargetDevice<T: TargetOperations + Sized> {
    ti: NonNull<bindings::dm_target>,
    dev: NonNull<bindings::dm_dev>,
    _p: PhantomData<*mut Target<T>>,
}

impl<T: TargetOperations> TargetDevice<T> {
    unsafe fn from_raw(ti: *mut bindings::dm_target, dd: *mut bindings::dm_dev) -> Self {
        // SAFETY: the caller should pass valid `dm_target` and `dm_dev`.
        unsafe {
            Self {
                ti: NonNull::new_unchecked(ti),
                dev: NonNull::new_unchecked(dd),
                _p: PhantomData,
            }
        }
    }

    /// Borrow the device mapper target.
    pub fn target(&self) -> &Target<T> {
        // SAFETY: the `from_raw` caller should pass valid `ti` pointer.
        unsafe { Target::borrow(self.ti.as_ptr()) }
    }

    /// Borrow the device mapper target mutably.
    pub fn mut_target(&mut self) -> &mut Target<T> {
        // SAFETY: the `from_raw` caller should pass valid `ti` pointer.
        unsafe { Target::borrow_mut(self.ti.as_ptr()) }
    }

    /// Return the device name.
    pub fn device_name(&self) -> &CStr {
        // SAFETY: the `from_raw` caller should pass valid `dev` pointer.
        unsafe {
            let name = (*self.dev.as_ptr()).name.as_ptr();
            CStr::from_char_ptr(name)
        }
    }

    /// Return the total device sectors.
    pub fn device_sectors(&self) -> usize {
        // SAFETY: the `from_raw` caller should pass valid `dev` pointer.
        unsafe { (*(*self.dev.as_ptr()).bdev).bd_nr_sectors as _ }
    }

    /// Return [NonNull<TargetDevice>].
    pub fn as_ptr(&mut self) -> NonNull<Self> {
        // SAFETY: `self` is non-null and valid.
        unsafe { NonNull::new_unchecked(self as *mut Self) }
    }

    /// Propagate report zones command to underlying devices.
    #[cfg(CONFIG_BLK_DEV_ZONED)]
    pub fn report_zones(
        &self,
        start: usize,
        sector: usize,
        args: &mut [ReportZonesArgs],
    ) -> Result {
        // SAFETY: the `from_raw` caller should pass valid `dev` pointer.
        unsafe {
            let bdev = (*self.dev.as_ptr()).bdev;
            let ptr = args.as_mut_ptr() as *mut bindings::dm_report_zones_args;
            to_result(bindings::dm_report_zones(
                bdev,
                start as _,
                sector as _,
                ptr,
                args.len() as _,
            ))
        }
    }

    /// Translate a device-relative logical-page-offset into an
    /// absolute physical pfn.
    ///
    /// Return the `addr` and the `pages` available for `DAX` at
    /// that pfn, if success.
    #[cfg(CONFIG_FS_DAX)]
    pub fn dax_direct_access(
        &mut self,
        pgoff: usize,
        nr_pages: usize,
        mode: DaxMode,
    ) -> Result<(usize, Range<usize>)> {
        let mut kaddr = core::ptr::null_mut();
        let mut pfn = bindings::pfn_t::default();

        // SAFETY: the `from_raw` caller should pass valid `dev` pointer.
        let count = unsafe {
            let dax_dev = (*self.dev.as_ptr()).dax_dev;
            bindings::dax_direct_access(
                dax_dev,
                pgoff as _,
                nr_pages as _,
                mode as _,
                &mut kaddr,
                &mut pfn,
            )
        };

        if count < 0 {
            Err(Error::from_errno(count as _))
        } else {
            let pages = Range {
                start: pfn.val as usize,
                end: (pfn.val as usize) + (count as usize),
            };
            Ok((kaddr as _, pages))
        }
    }

    /// Zero page range.
    #[cfg(CONFIG_FS_DAX)]
    pub fn dax_zero_page_range(&mut self, pgoff: usize, nr_pages: usize) -> Result {
        // SAFETY: the `from_raw` caller should pass valid `dev` pointer.
        unsafe {
            let dax_dev = (*self.dev.as_ptr()).dax_dev;
            to_result(bindings::dax_zero_page_range(dax_dev, pgoff as _, nr_pages))
        }
    }

    /// Recover a poisoned range by DAX device driver capable of
    /// clearing poison.
    #[cfg(CONFIG_FS_DAX)]
    pub fn dax_recovery_write(
        &mut self,
        iov_iter: Pin<&mut IovIter>,
        pgoff: usize,
        region: Range<usize>,
    ) -> usize {
        // SAFETY: the `from_raw` caller should pass `dev` pointer.
        unsafe {
            let dax_dev = (*self.dev.as_ptr()).dax_dev;
            let i = iov_iter.opaque.get();
            bindings::dax_recovery_write(dax_dev, pgoff as _, region.start as _, region.len(), i)
        }
    }
}

impl<T: TargetOperations> Drop for TargetDevice<T> {
    fn drop(&mut self) {
        // SAFETY: the `from_raw` caller should pass valid `ti` and `dev`.
        unsafe { bindings::dm_put_device(self.ti.as_ptr(), self.dev.as_ptr()) }
    }
}

/// Gather info about underlying device of target.
///
/// The first is the [`TargetDevice`], the second is the start sector of
/// the device, and the third is the length (in sectors) of the device.
pub type IterDevice<T> = (NonNull<TargetDevice<T>>, usize, usize);

/// The return values of target map function, i.e., [`TargetOperations::map`].
#[repr(u32)]
pub enum MapState {
    /// The target will handle the io by resubmitting it later.
    Submitted = bindings::DM_MAPIO_SUBMITTED,

    /// Simple remap complete.
    Remapped = bindings::DM_MAPIO_REMAPPED,

    /// The target wants to requeue the io.
    Requeue = bindings::DM_MAPIO_REQUEUE,

    /// The target wants to requeue the io after a delay.
    DelayRequeue = bindings::DM_MAPIO_DELAY_REQUEUE,

    /// The target wants to complete the io.
    Kill = bindings::DM_MAPIO_KILL,
}

/// The return values of target end_io function.
#[repr(u32)]
pub enum EndState {
    /// Ended successfully.
    Done = bindings::DM_ENDIO_DONE,

    /// The io has still not completed (eg, multipath target might
    /// want to requeue a failed io).
    Incomplete = bindings::DM_ENDIO_INCOMPLETE,

    /// The target wants to requeue the io.
    Requeue = bindings::DM_ENDIO_REQUEUE,

    /// The target wants to requeue the io after a delay.
    DelayRequeue = bindings::DM_ENDIO_DELAY_REQUEUE,
}

/// Wrap the c struct `map_info`.
pub struct MapInfo(Opaque<bindings::map_info>);

impl MapInfo {
    unsafe fn borrow_mut<'a>(ptr: *mut bindings::map_info) -> &'a mut Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &mut *(ptr as *mut Self) }
    }
}

/// Define target status types.
#[repr(u32)]
pub enum StatusType {
    /// Request for some general info.
    Info,

    /// Request for more detailed info.
    Table,

    /// Request for some integrity info.
    Ima,

    /// Undefined.
    Undefined,
}

impl From<u32> for StatusType {
    fn from(value: u32) -> Self {
        match value {
            bindings::status_type_t_STATUSTYPE_INFO => Self::Info,
            bindings::status_type_t_STATUSTYPE_TABLE => Self::Table,
            bindings::status_type_t_STATUSTYPE_IMA => Self::Ima,
            _ => Self::Undefined,
        }
    }
}

/// Define target status flags.
#[repr(u32)]
pub enum StatusFlags {
    /// See `DM_STATUS_NOFLUSH_FLAG`.
    NoFlush = 1 << 0,

    /// Undefined.
    Undefined,
}

impl From<u32> for StatusFlags {
    fn from(value: u32) -> Self {
        match value {
            0 => Self::NoFlush,
            _ => Self::Undefined,
        }
    }
}

/// Wrap the kernel struct `dm_report_zones_args`.
pub struct ReportZonesArgs(Opaque<bindings::dm_report_zones_args>);

impl ReportZonesArgs {
    unsafe fn borrow_mut<'a>(ptr: *mut bindings::dm_report_zones_args) -> &'a mut Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &mut *(ptr as *mut Self) }
    }

    /// Return the next sector.
    pub fn next_sector(&self) -> usize {
        // SAFETY: `self.0` is borrowed form foreign pointer,
        // should be valid.
        unsafe { (*self.0.get()).next_sector as _ }
    }
}

/// Wrap the `c_char` arguments, which yields `CStr`.
pub struct Args {
    argc: core::ffi::c_uint,
    argv: *mut *mut core::ffi::c_char,
}

impl Args {
    /// The caller should ensure that the number of valid `argv` pointers
    /// should be exactly `argc`.
    unsafe fn new(argc: core::ffi::c_uint, argv: *mut *mut core::ffi::c_char) -> Self {
        Self { argc, argv }
    }

    /// Return the number of arguments.
    pub fn len(&self) -> usize {
        self.argc as _
    }

    /// Return the `nth` (from zero) argument.
    ///
    /// If the index is out of bounds, return `None`.
    pub fn get(&self, index: usize) -> Option<&CStr> {
        if self.argc == 0 || index >= self.argc as _ {
            None
        } else {
            // SAFETY: the `new` caller should ensure the number of valid `argv`.
            unsafe { Some(CStr::from_char_ptr(*self.argv.add(index))) }
        }
    }
}

impl Index<usize> for Args {
    type Output = CStr;

    /// When using the indexing operator(`[]`), the caller should check the
    /// length of [`Args`]. If the index is out of bounds, this will [`panic`].
    fn index(&self, index: usize) -> &Self::Output {
        if self.argc == 0 || index >= self.argc as _ {
            panic!(
                "Index out of bounds: the length is {} but the index is {}.",
                self.argc, index
            )
        } else {
            // SAFETY: the `new` caller should ensure the number of valid `argv`.
            unsafe { CStr::from_char_ptr(*self.argv.add(index)) }
        }
    }
}

/// Wrap the kernel struct `bio`.
///
/// Dummy.
#[pin_data]
pub struct Bio {
    #[pin]
    opaque: Opaque<bindings::bio>,
}

impl Bio {
    unsafe fn from_raw<'a>(ptr: *mut bindings::bio) -> Pin<&'a mut Self> {
        // SAFETY: the caller should pass a valid `bio` pointer.
        unsafe { Pin::new_unchecked(&mut *(ptr as *mut Self)) }
    }

    fn op_and_flags(&self) -> u32 {
        // SAFETY: the `from_raw` caller should pass valid `bio`, so
        // `self.opaque` is valid too.
        unsafe { (*self.opaque.get()).bi_opf }
    }

    /// Return `true` if the bio request is write.
    pub fn is_write(&self) -> bool {
        self.op_and_flags() & bindings::req_op_REQ_OP_WRITE != 0
    }

    /// Return the start sector of bio.
    pub fn sector(&self) -> usize {
        // SAFETY: the `from_raw` caller should pass valid `bio`, so
        // `self.opaque` is valid too.
        unsafe { (*self.opaque.get()).bi_iter.bi_sector as _ }
    }

    /// Set the start sector of bio.
    pub fn set_sector(self: &Pin<&mut Self>, sector: usize) {
        // SAFETY: the `from_raw` caller should pass valid `bio`, so
        // `self.opaque` is valid too.
        unsafe {
            (*self.opaque.get()).bi_iter.bi_sector = sector as _;
        }
    }

    /// Set the block device of bio.
    pub fn set_dev<T: TargetOperations>(self: &Pin<&mut Self>, td: &TargetDevice<T>) {
        // SAFETY: the `from_raw` caller should pass valid `bio`, so
        // `self.opaque` is valid too.
        unsafe {
            bindings::bio_set_dev(self.opaque.get(), (*td.dev.as_ptr()).bdev);
        }
    }
}

/// Wrap the kernel struct `request`.
///
/// Dummy.
#[pin_data]
pub struct Request {
    #[pin]
    opaque: Opaque<bindings::request>,
}

impl Request {
    unsafe fn from_raw<'a>(ptr: *mut bindings::request) -> Pin<&'a mut Self> {
        // SAFETY: the caller should pass a valid `request` pointer.
        unsafe { Pin::new_unchecked(&mut *(ptr as *mut Self)) }
    }
}

/// Wrap the block error status values (see [blk_status_t]).
///
/// [`blk_status_t`]: ../../../../include/linux/blk_types.h
#[repr(u32)]
#[allow(missing_docs)]
pub enum BlkStatus {
    Ok,
    NotSupp,
    TimeOut,
    NoSpc,
    Transport,
    Target,
    Nexus,
    Medium,
    Protection,
    Resource,
    IoErr,
    DmRequeue,
    Again,
    DevResource,
    ZoneResource,
    ZoneOpenResource,
    ZoneActiveResource,
    Offline,
    Undefined,
}

impl From<u32> for BlkStatus {
    fn from(value: u32) -> Self {
        match value {
            0 => Self::Ok,
            1 => Self::NotSupp,
            2 => Self::TimeOut,
            3 => Self::NoSpc,
            4 => Self::Transport,
            5 => Self::Target,
            6 => Self::Nexus,
            7 => Self::Medium,
            8 => Self::Protection,
            9 => Self::Resource,
            10 => Self::IoErr,
            11 => Self::DmRequeue,
            12 => Self::Again,
            13 => Self::DevResource,
            14 => Self::ZoneResource,
            15 => Self::ZoneOpenResource,
            16 => Self::ZoneActiveResource,
            17 => Self::Offline,
            _ => Self::Undefined,
        }
    }
}

/// Wrap the kernel struct `queue_limits`.
///
/// Dummy.
pub struct QueueLimits(Opaque<bindings::queue_limits>);

impl QueueLimits {
    unsafe fn borrow_mut<'a>(ptr: *mut bindings::queue_limits) -> &'a mut Self {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { &mut *(ptr as *mut Self) }
    }
}

/// Define dax direct_access mode.
pub enum DaxMode {
    /// Normal dax access.
    Access,

    /// Recovery write.
    RecoveryWrite,

    /// Undefined.
    Undefined,
}

impl From<i32> for DaxMode {
    fn from(value: i32) -> Self {
        match value {
            bindings::dax_access_mode_DAX_ACCESS => Self::Access,
            bindings::dax_access_mode_DAX_RECOVERY_WRITE => Self::RecoveryWrite,
            _ => Self::Undefined,
        }
    }
}

/// Wrap the kernel struct `iov_iter`.
///
/// Dummy.
#[allow(dead_code)]
#[pin_data]
pub struct IovIter {
    #[pin]
    opaque: Opaque<bindings::iov_iter>,
}

impl IovIter {
    unsafe fn from_raw<'a>(ptr: *mut bindings::iov_iter) -> Pin<&'a mut Self> {
        // SAFETY: the caller should pass a valid `ptr`.
        unsafe { Pin::new_unchecked(&mut *(ptr as *mut Self)) }
    }
}
