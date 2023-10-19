// SPDX-License-Identifier: GPL-2.0

//! Crypto API.
//!
//! C header: [`include/linux/crypto.h`](../../../../include/linux/crypto.h)
//!
//! Reference: <https://www.kernel.org/doc/html/latest/crypto/index.html>

pub mod aead;
pub mod skcipher;

/// Produces a pointer to an object from a pointer to one of its fields.
///
/// # Safety
///
/// Callers must ensure that the pointer to the field is in fact a pointer to the specified field,
/// as opposed to a pointer to another object of the same type. If this condition is not met,
/// any dereference of the resulting pointer is UB.
///
/// # Examples
///
/// ```
/// # use kernel::container_of;
/// struct Test {
///     a: u64,
///     b: u32,
/// }
///
/// let test = Test { a: 10, b: 20 };
/// let b_ptr = &test.b;
/// let test_alias = container_of!(b_ptr, Test, b);
/// assert!(core::ptr::eq(&test, test_alias));
/// ```
#[macro_export]
macro_rules! container_of {
    ($ptr:expr, $type:ty, $($f:tt)*) => {{
        let ptr = $ptr as *const _ as *const u8;
        let offset = core::mem::offset_of!($type, $($f)*);
        ptr.wrapping_sub(offset) as *const $type
    }}
}