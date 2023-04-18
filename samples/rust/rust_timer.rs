// SPDX-License-Identifier: GPL-2.0

//! Rust timer sample.

use core::sync::atomic::{AtomicU32, Ordering};
use core::time::Duration;
use kernel::prelude::*;
use kernel::{sync::UniqueArc, timer::Timer};

module! {
    type: RustTimer,
    name: "rust_timer",
    author: "Rust for Linux Contributors",
    description: "Rust timer sample",
    license: "GPL",
}

struct RustTimer {
    adapter: UniqueArc<Adapter>,
}

struct Adapter {
    counter: AtomicU32,
    timer: Timer,
}

kernel::impl_self_timer_adapter!(Adapter, timer, |a| {
    let count = a.counter.fetch_add(1, Ordering::Relaxed);
    pr_info!("Called with count={}\n", count);
    if count < 10 {
        a.timer.delay(Duration::from_millis(1000));
    }
});

impl kernel::Module for RustTimer {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        pr_info!("Rust timer sample (init)\n");

        let adapter = UniqueArc::try_new(Adapter {
            counter: AtomicU32::new(0),
            // SAFETY: `init_timer_item!` is called below.
            timer: unsafe { Timer::new() },
        })?;
        kernel::init_timer_item!(&adapter);

        adapter.timer.delay(Duration::from_millis(1000));

        Ok(RustTimer { adapter })
    }
}

impl Drop for RustTimer {
    fn drop(&mut self) {
        pr_info!(
            "My counter is {}\n",
            self.adapter.counter.load(Ordering::Relaxed)
        );
        pr_info!("Rust timer sample (exit)\n");
    }
}
