// SPDX-License-Identifier: GPL-2.0

//! Skcipher.
//!
//! C header: [`include/crypto/skcipher.h`](../../../../../include/crypto/skcipher.h)

use core::ptr::addr_of_mut;

use crate::error::{from_err_ptr, to_result};
use crate::scatterlist::ScatterList;
use crate::str::CStr;
use crate::{container_of, prelude::*};
use crate::{new_mutex, sync::Mutex};

/// A Symmetric Key Cipher wrapper.
///
/// The `crypto_skcipher` and `skcipher_request` pointer is constructed by the `new` initializer.
/// The recommended way to create such instances is with the [`pin_init`].
///
/// # Examples
///
/// The following is examples of creating [`Cipher`] instances.
///
/// ```rust
/// use kernel::{c_str, stack_try_pin_init};
/// # use core::pin::Pin;
/// # use kernel::crypto::skcipher::Cipher;
///
/// // Allocates an instance on stack.
/// stack_try_pin_init!(let foo = Cipher::new(c_str!("cbc(aes)"), 0, 0));
/// let foo: Result<Pin<&mut Cipher>> = foo;
///
/// // Alloccate an instance by Box::pin_init.
/// let bar: Result<Pin<Box<Cipher>>> = Box::pin_init(Cipher::new(c_str!("cbc(aes)"), 0, 0));
/// ```
#[pin_data(PinnedDrop)]
pub struct Cipher {
    #[pin]
    lock: Mutex<()>,
    skcipher: *mut bindings::crypto_skcipher,
    request: *mut bindings::skcipher_request,
}

// SAFETY: `Cipher` is synchronized `Mutex`, so it's safe to be used on multiple threads
// concurrently.
unsafe impl Sync for Cipher {}

impl Cipher {
    /// Constructs a new initializer.
    ///
    /// Try to allocate an skcipher handler, `alg_name` specifies the driver name of the cipher,
    /// `type_` specifies the type of the cipher, `mask` specifies the mask for the cipher.
    ///
    /// Returns a type impl [`PinInit<Cipher>`] in case of success, or an error code in [`Error`].
    pub fn new(alg_name: &'static CStr, type_: u32, mask: u32) -> impl PinInit<Self, Error> {
        try_pin_init!(&this in Self {
            lock <- new_mutex!(()),
            skcipher: from_err_ptr(
                // SAFETY: `alg_name` has static lifetimes and live indefinitely. Any error will
                // be catched by `from_err_ptr`.
                unsafe { bindings::crypto_alloc_skcipher(alg_name.as_char_ptr(), type_, mask) }
            )?,
            request: {
                // SAFETY: `this` is a valid when the macro is called. And `skcipher` is initialized
                // above, so it's also valid.
                let ptr = unsafe {
                    bindings::skcipher_request_alloc(
                        (*this.as_ptr()).skcipher,
                        bindings::GFP_KERNEL | bindings::__GFP_ZERO,
                    )
                };
                if ptr.is_null() {
                    // SAFETY: `skcipher` is valid and initialized above, so its memory can be
                    // safely deallocated.
                    unsafe {
                        let skcipher = (*this.as_ptr()).skcipher;
                        let base = addr_of_mut!((*skcipher).base);
                        bindings::crypto_destroy_tfm(skcipher as *mut core::ffi::c_void, base);
                    }
                    return Err(ENOMEM);
                }
                ptr
            },
        })
    }

    /// Returns the size (in bytes) of the IV for the skcipher referenced by the cipher handle. This IV
    /// size may be zero if the cipher does not need an IV.
    pub fn ivsize(&self) -> u32 {
        // SAFETY: `skcipher` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let crypto_alg = (*self.skcipher).base.__crt_alg;
            let skcipher_alg = container_of!(crypto_alg, bindings::skcipher_alg, base);
            (*skcipher_alg).ivsize
        }
    }

    /// Returns the size (in bytes) of the request data structure. The skcipher_request data structure
    /// contains all pointers to data required for the skcipher operation.
    pub fn reqsize(&self) -> u32 {
        // SAFETY: `skcipher` is constructed by the `new` constructor, so it's valid.
        unsafe { (*self.skcipher).reqsize }
    }

    /// Returns the block size (in bytes) for the skcipher referenced with the cipher handle. The caller
    /// may use that information to allocate appropriate memory for the data returned by the encryption
    /// or decryption operation.
    pub fn blocksize(&self) -> u32 {
        // SAFETY: `skcipher` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let crypto_alg = (*self.skcipher).base.__crt_alg;
            (*crypto_alg).cra_blocksize
        }
    }

    /// Set key for skcipher.
    ///
    /// The key length determines the cipher type. Many block ciphers implement different cipher
    /// modes depending on the key size, such as AES-128 vs AES-192 vs. AES-256. When providing a
    /// 16 byte key for an AES cipher handle, AES-128 is performed.
    ///
    /// Returns `Ok(())` if the setting of the key was successful, or an error code in [`Error`].
    fn set_key(&self, key: Pin<&[u8]>) -> Result {
        // SAFETY: `skcipher` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err = bindings::crypto_skcipher_setkey(
                self.skcipher,
                key.get_ref().as_ptr(),
                key.get_ref().len() as u32,
            );
            to_result(err)
        }
    }

    /// Set information needed to perform the cipher operation.
    ///
    /// Setting the `src` and `dst` scatterlists which hold the plaintext or ciphertext. The `cryptlen`
    /// specifies the number of bytes to process from `src`, and `iv` specifies the IV for the cipher
    /// operation which must comply with the IV size defined by `ivsize` method.
    ///
    /// For encryption, the source is treated as the plaintext and the destination is the ciphertext.
    /// For a decryption operation, the use is reversed.
    fn set_crypt(
        &self,
        src: Pin<&ScatterList<'_>>,
        dst: Pin<&mut ScatterList<'_>>,
        cryptlen: u32,
        iv: Pin<&mut [u8]>,
    ) {
        // SAFETY: `request` is constructed by the `new` constructor, so it's valid. The `src`,
        // `dst` and `iv` are also valid and pinned.
        unsafe {
            let req_src = addr_of_mut!((*self.request).src);
            *req_src = src.as_ref().as_mut_ptr();
            let req_dst = addr_of_mut!((*self.request).dst);
            *req_dst = dst.as_ref().as_mut_ptr();
            let req_cryptlen = addr_of_mut!((*self.request).cryptlen);
            *req_cryptlen = cryptlen;
            let req_iv = addr_of_mut!((*self.request).iv);
            *req_iv = iv.get_mut().as_mut_ptr();
        }
    }

    /// Encrypt plaintext.
    ///
    /// `src`: source data scatterlist, holds the `plaintext`;
    /// `dst`:  destination data scatterlist, holds the `ciphertext`;
    /// `cryptlen`: the number of bytes to process from `src`;
    /// `key`: the symmetric key, used for the cipher operation;
    /// `iv`: the Initialization Vector for the cipher operation, may be modified.
    ///
    /// Returns `Ok(())` if the cipher operation was successful, or an error code in [`Error`].
    pub fn encrypt(
        &self,
        src: Pin<&ScatterList<'_>>,
        dst: Pin<&mut ScatterList<'_>>,
        cryptlen: u32,
        key: Pin<&[u8]>,
        iv: Pin<&mut [u8]>,
    ) -> Result {
        let _lock = self.lock.lock();
        self.set_key(key)?;
        self.set_crypt(src, dst, cryptlen, iv);
        // SAFETY: `request` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err = bindings::crypto_skcipher_encrypt(self.request);
            to_result(err)
        }
    }

    /// Decrypt ciphertext.
    ///
    /// `src`: source data scatterlist, holds the `ciphertext`;
    /// `dst`:  destination data scatterlist, holds the `plaintext`;
    /// `cryptlen`: the number of bytes to process from `src`;
    /// `key`: the symmetric key, used for the cipher operation;
    /// `iv`: the Initialization Vector for the cipher operation, may be modified.
    ///
    /// Returns `Ok(())` if the cipher operation was successful, or an error code in [`Error`].
    pub fn decrypt(
        &self,
        src: Pin<&ScatterList<'_>>,
        dst: Pin<&mut ScatterList<'_>>,
        cryptlen: u32,
        key: Pin<&[u8]>,
        iv: Pin<&mut [u8]>,
    ) -> Result {
        let _lock = self.lock.lock();
        self.set_key(key)?;
        self.set_crypt(src, dst, cryptlen, iv);
        // SAFETY: `request` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err = bindings::crypto_skcipher_decrypt(self.request);
            to_result(err)
        }
    }
}

#[pinned_drop]
impl PinnedDrop for Cipher {
    fn drop(self: Pin<&mut Self>) {
        let skcipher = self.as_ref().get_ref().skcipher;
        let request = self.as_ref().get_ref().request;
        // SAFETY: `skcipher` and `request` is constructed by the `new` constructor,
        // so they are valid.
        unsafe {
            let base = addr_of_mut!((*skcipher).base);
            bindings::crypto_destroy_tfm(skcipher as *mut core::ffi::c_void, base);
            bindings::kfree_sensitive(request as *const core::ffi::c_void)
        }
    }
}