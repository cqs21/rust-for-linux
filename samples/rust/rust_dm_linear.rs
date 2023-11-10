// SPDX-License-Identifier: GPL-2.0

//! Rust device mapper linear target sample.
//!
//! C version: drivers/md/dm-linear.c

use core::ops::Range;
use core::ptr::NonNull;
use kernel::bindings::PAGE_SECTORS_SHIFT;
use kernel::device_mapper::*;
use kernel::prelude::*;
use kernel::{c_str, fmt, str::CString};

module! {
    type: RustDmLinear,
    name: "rust_dm_linear",
    author: "Rust for Linux Contributors",
    description: "Rust device mapper linear target sample",
    license: "GPL",
}

struct Linear {
    dev: TargetDevice<Self>,
    start: usize,
}

impl Linear {
    fn new(dev: TargetDevice<Self>, start: usize) -> impl Init<Self> {
        init!(Self { dev, start })
    }

    fn map_sector(&self, sector: usize, base: usize) -> usize {
        sector - base + self.start
    }
}

// SAFETY: `Linear` could be used from all threads.
unsafe impl Sync for Linear {}

#[vtable]
impl TargetOperations for Linear {
    type Private = Linear;

    fn ctr(t: &mut Target<Self>, args: Args) -> Result<Box<Linear>> {
        if args.len() != 2 {
            t.set_error(c_str!("Invalid argument count"));
            return Err(EINVAL);
        }

        let dev = match t.get_device(&args[0]) {
            Ok(dev) => dev,
            Err(e) => {
                t.set_error(c_str!("Device lookup failed"));
                return Err(e);
            }
        };

        let start = &args[1].to_str().map_err(|_| EINVAL)?;
        let start = usize::from_str_radix(start, 10).map_err(|_| {
            t.set_error(c_str!("Invalid device sector"));
            EINVAL
        })?;

        t.set_num_flush_bios(1);
        t.set_num_discard_bios(1);
        t.set_num_secure_erase_bios(1);
        t.set_num_write_zeroes_bios(1);

        Box::init(Linear::new(dev, start))
    }

    fn dtr(_: &mut Target<Self>) {}

    fn map(t: &mut Target<Self>, mut bio: Pin<&mut Bio>) -> MapState {
        let Some(linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return MapState::Kill;
        };

        let offset = bio.sector() - linear.dev.target().begin_sector();
        bio.set_dev(&linear.dev);
        bio.set_sector(linear.start + offset);
        MapState::Remapped
    }

    fn status(t: &mut Target<Self>, type_: StatusType, _: StatusFlags) -> Option<CString> {
        let Some(linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return None;
        };

        match type_ {
            StatusType::Info => None,
            StatusType::Table => {
                CString::try_from_fmt(fmt!("{} {}", linear.dev.device_name(), linear.start)).ok()
            }
            StatusType::Ima => {
                let version = linear.dev.target().version();
                CString::try_from_fmt(fmt!(
                    "target_name={},target_version={}.{}.{},device_name={},start={};",
                    linear.dev.target().name(),
                    version[0],
                    version[1],
                    version[2],
                    linear.dev.device_name(),
                    linear.start
                ))
                .ok()
            }
            _ => {
                pr_warn!("Unsupported dm_status_type\n");
                None
            }
        }
    }

    fn prepare_ioctl(t: &mut Target<Self>) -> (i32, Option<NonNull<TargetDevice<Self>>>) {
        let Some(mut linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return (EINVAL.to_errno(), None);
        };

        let mut ret = 0;
        if linear.start > 0 || linear.dev.target().total_sectors() != linear.dev.device_sectors() {
            ret = 1;
        }
        (ret, Some(linear.dev.as_ptr()))
    }

    fn iterate_devices(t: &mut Target<Self>) -> Result<Box<dyn Iterator<Item = IterDevice<Self>>>> {
        let Some(mut linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return Err(EINVAL);
        };

        Ok(Box::init(IterLinear::new(
            linear.dev.as_ptr(),
            linear.start,
            t.total_sectors(),
        ))?)
    }

    #[cfg(CONFIG_BLK_DEV_ZONED)]
    fn report_zones(t: &mut Target<Self>, args: &mut [ReportZonesArgs]) -> Result {
        if args.len() == 0 {
            pr_warn!("Invalid report_zones_args\n");
            return Err(EINVAL);
        }

        let Some(linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return Err(EINVAL);
        };

        let sector = linear.map_sector(args[0].next_sector(), linear.dev.target().begin_sector());
        linear.dev.report_zones(linear.start, sector, args)
    }

    #[cfg(CONFIG_FS_DAX)]
    fn direct_access(
        t: &mut Target<Self>,
        pgoff: usize,
        nr_pages: usize,
        mode: DaxMode,
    ) -> Result<(usize, Range<usize>)> {
        let base = t.begin_sector();
        let Some(mut linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return Err(EINVAL);
        };

        let sector = linear.map_sector(pgoff << PAGE_SECTORS_SHIFT, base);
        let offset = (linear.dev.device_sectors() + sector) >> PAGE_SECTORS_SHIFT;
        linear.dev.dax_direct_access(offset, nr_pages, mode)
    }

    #[cfg(CONFIF_FS_DAX)]
    fn dax_zero_page_range(t: &mut Target<Self>, pgoff: usize, nr_pages: usize) -> Result {
        let base = t.begin_sector();
        let Some(mut linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return Err(EINVAL);
        };

        let sector = linear.map_sector(pgoff << PAGE_SECTORS_SHIFT, base);
        let offset = (linear.dev.device_sectors() + sector) >> PAGE_SECTORS_SHIFT;
        linear.dev.dax_zero_page_range(offset, nr_pages)
    }

    #[cfg(CONFIF_FS_DAX)]
    fn dax_recovery_write(
        t: &mut Target<Self>,
        iov_iter: Pin<&mut IovIter>,
        pgoff: usize,
        region: Range<usize>,
    ) -> usize {
        let base = t.begin_sector();
        let Some(mut linear) = t.private() else {
            pr_warn!("Error, found no rust_linear\n");
            return 0;
        };

        let sector = linear.map_sector(pgoff << PAGE_SECTORS_SHIFT, base);
        let offset = (linear.dev.device_sectors() + sector) >> PAGE_SECTORS_SHIFT;
        linear.dev.dax_recovery_write(iov_iter, offset, region)
    }
}

struct IterLinear {
    item: Option<IterDevice<Linear>>,
}

impl IterLinear {
    fn new(dev: NonNull<TargetDevice<Linear>>, start: usize, len: usize) -> impl Init<Self> {
        init!(Self {
            item: Some((dev, start, len))
        })
    }
}

impl Iterator for IterLinear {
    type Item = IterDevice<Linear>;

    fn next(&mut self) -> Option<Self::Item> {
        self.item.take()
    }
}

struct RustDmLinear(Pin<Box<TargetType>>);

impl kernel::Module for RustDmLinear {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("Rust device mapper linear target sample (init)\n");

        let target = Box::pin_init(TargetType::register::<Linear>(
            _module,
            c_str!("rust_linear"),
            [0, 0, 1],
            0,
        ));

        let target = match target {
            Ok(target) => target,
            Err(e) => {
                pr_warn!("Target register failed, errno: {}\n", e.to_errno());
                return Err(e);
            }
        };
        Ok(RustDmLinear(target))
    }
}

impl Drop for RustDmLinear {
    fn drop(&mut self) {
        pr_info!("Rust device mapper linear target sample (exit)\n");
    }
}
