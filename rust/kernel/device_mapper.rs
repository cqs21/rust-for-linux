// SPDX-License-Identifier: GPL-2.0

//! Device Mapper.
//!
//! C header: [`include/linux/device-mapper.h`](../../../../include/linux/device-mapper.h)

use core::marker::PhantomData;
use core::ops::Index;
use core::ptr::{addr_of, NonNull};

use crate::error::to_result;
use crate::prelude::*;
use crate::str::CStr;
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
}

impl<T: TargetOperations> Drop for TargetDevice<T> {
    fn drop(&mut self) {
        // SAFETY: the `from_raw` caller should pass valid `ti` and `dev`.
        unsafe { bindings::dm_put_device(self.ti.as_ptr(), self.dev.as_ptr()) }
    }
}

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
        unsafe { Pin::new(&mut *(ptr as *mut Self)) }
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
