// SPDX-License-Identifier: GPL-2.0

//! AEAD.
//!
//! C header: [`include/crypto/aead.h`](../../../../../include/crypto/aead.h)

use core::ptr::addr_of_mut;

use crate::error::{from_err_ptr, to_result};
use crate::scatterlist::ScatterList;
use crate::str::CStr;
use crate::{container_of, prelude::*};
use crate::{new_mutex, sync::Mutex};

/// An Authenticated Encryption With Associated Data (AEAD) wrapper.
///
/// The `crypto_aead` and `aead_request` pointer is constructed by the `new` initializer.
/// The recommended way to create such instances is with the [`pin_init`].
///
/// # Examples
///
/// The following is examples of creating [`Cipher`] instances.
///
/// ```rust
/// use kernel::{c_str, stack_try_pin_init};
/// # use core::pin::Pin;
/// # use kernel::crypto::aead::Cipher;
///
/// // Allocates an instance on stack.
/// stack_try_pin_init!(let foo = Cipher::new(c_str!("gcm(aes)"), 0, 0));
/// let foo: Result<Pin<&mut Cipher>> = foo;
///
/// // Alloccate an instance by Box::pin_init.
/// let bar: Result<Pin<Box<Cipher>>> = Box::pin_init(Cipher::new(c_str!("gcm(aes)"), 0, 0));
/// ```
#[pin_data(PinnedDrop)]
pub struct Cipher {
    #[pin]
    lock: Mutex<()>,
    aead: *mut bindings::crypto_aead,
    request: *mut bindings::aead_request,
}

// SAFETY: `Cipher` is synchronized `Mutex`, so it's safe to be used on multiple threads
// concurrently.
unsafe impl Sync for Cipher {}

impl Cipher {
    /// Constructs a new initializer.
    ///
    /// Try to allocate an AEAD cipher handler, `alg_name` specifies the driver name of the cipher,
    /// `type_` specifies the type of the cipher, `mask` specifies the mask for the cipher.
    ///
    /// Returns a type impl [`PinInit<Cipher>`] in case of success, or an error code in [`Error`].
    pub fn new(alg_name: &'static CStr, type_: u32, mask: u32) -> impl PinInit<Self, Error> {
        try_pin_init!(&this in Self {
            lock <- new_mutex!(()),
            aead: from_err_ptr(
                // SAFETY: `alg_name` has static lifetimes and live indefinitely. Any error will
                // be catched by `from_err_ptr`.
                unsafe { bindings::crypto_alloc_aead(alg_name.as_char_ptr(), type_, mask) }
            )?,
            request: {
                // SAFETY: `this` is a valid when the macro is called. And `aead` is initialized
                // above, so it's also valid.
                let ptr = unsafe {
                    bindings::aead_request_alloc(
                        (*this.as_ref()).aead,
                        bindings::GFP_KERNEL | bindings::__GFP_ZERO,
                    )
                };
                if ptr.is_null() {
                    // SAFETY: `aead` is valid and initialized above, so its memory can be
                    // safely deallocated.
                    unsafe {
                        let aead = (*this.as_ref()).aead;
                        let base = addr_of_mut!((*aead).base);
                        bindings::crypto_destroy_tfm(aead as *mut core::ffi::c_void, base);
                    }
                    return Err(ENOMEM);
                }
                ptr
            },
        })
    }

    /// Returns the size (in bytes) of the IV for the aead referenced by the cipher handle. This IV
    /// size may be zero if the cipher does not need an IV.
    pub fn ivsize(&self) -> u32 {
        // SAFETY: `aead` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let crypto_alg = (*self.aead).base.__crt_alg;
            let aead_alg = container_of!(crypto_alg, bindings::aead_alg, base);
            (*aead_alg).ivsize
        }
    }

    /// Returns the maximum size (in bytes) of the authentication data for the AEAD cipher referenced
    /// by the AEAD cipher handle. The authentication data size may be zero if the cipher implements
    /// a hard-coded maximum.
    pub fn authsize(&self) -> u32 {
        // SAFETY: `aead` is constructed by the `new` constructor, so it's valid.
        unsafe { (*self.aead).authsize }
    }

    /// Returns the size (in bytes) of the request data structure. The aead_request data structure
    /// contains all pointers to data required for the AEAD cipher operation.
    pub fn reqsize(&self) -> u32 {
        // SAFETY: `aead` is constructed by the `new` constructor, so it's valid.
        unsafe { (*self.aead).reqsize }
    }

    /// Returns the block size (in bytes) for the AEAD referenced with the cipher handle. The caller
    /// may use that information to allocate appropriate memory for the data returned by the encryption
    /// or decryption operation.
    pub fn blocksize(&self) -> u32 {
        // SAFETY: `aead` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let crypto_alg = (*self.aead).base.__crt_alg;
            (*crypto_alg).cra_blocksize
        }
    }

    /// Set authentication data size.
    ///
    /// AEAD requires an authentication tag (or MAC) in addition to the associated data.
    ///
    /// Returns `Ok(())` if the setting of the authsize was successful, or an error code in [`Error`].
    pub fn set_authsize(&self, authsize: u32) -> Result {
        let _lock = self.lock.lock();
        // SAFETY: `aead` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err = bindings::crypto_aead_setauthsize(self.aead, authsize);
            to_result(err)
        }
    }

    /// Set key for AEAD cipher.
    ///
    /// The key length determines the cipher type. Many block ciphers implement different cipher
    /// modes depending on the key size, such as AES-128 vs AES-192 vs. AES-256. When providing a
    /// 16 byte key for an AES cipher handle, AES-128 is performed.
    ///
    /// Returns `Ok(())` if the setting of the key was successful, or an error code in [`Error`].
    fn set_key(&self, key: Pin<&[u8]>) -> Result {
        // SAFETY: `aead` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err =
                bindings::crypto_aead_setkey(self.aead, key.get_ref().as_ptr(), key.len() as u32);
            to_result(err)
        }
    }

    /// Set information needed to perform the cipher operation.
    ///
    /// Setting the `src` and `dst` scatterlists which hold the associated data concatenated with
    /// the plaintext or ciphertext. And `assoclen` specifies the length of associated data in `src`,
    /// `cryptlen` specifies the number of bytes to process from `src`(FIXME), `iv` specifies the IV
    /// for the cipher operation which must comply with the IV size defined by `ivsize` method.
    ///
    /// The memory structure for cipher operation has the following structure:
    ///
    /// - AEAD encryption input:  assoc data || plaintext
    /// - AEAD encryption output: assoc data || ciphertext || auth tag
    /// - AEAD decryption input:  assoc data || ciphertext || auth tag
    /// - AEAD decryption output: assoc data || plaintext
    fn set_crypt(
        &self,
        src: Pin<&ScatterList<'_>>,
        dst: Pin<&mut ScatterList<'_>>,
        assoclen: u32,
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
            let req_assoclen = addr_of_mut!((*self.request).assoclen);
            *req_assoclen = assoclen;
            let req_cryptlen = addr_of_mut!((*self.request).cryptlen);
            *req_cryptlen = cryptlen;
            let req_iv = addr_of_mut!((*self.request).iv);
            *req_iv = iv.get_mut().as_mut_ptr();
        }
    }

    /// Encrypt plaintext.
    ///
    /// `src`: source data scatterlist, holds the `assoc data || plaintext`;
    /// `dst`:  destination data scatterlist, holds the `assoc data || ciphertext || auth tag`;
    /// `assoclen`: the length (in bytes) of `assoc data`;
    /// `cryptlen`: the length (in bytes) of `plaintext`;
    /// `key`: the symmetric key, used for the cipher operation;
    /// `iv`: the Initialization Vector for the cipher operation, may be modified.
    ///
    /// Returns `Ok(())` if the cipher operation was successful, or an error code in [`Error`].
    pub fn encrypt(
        &self,
        src: Pin<&ScatterList<'_>>,
        dst: Pin<&mut ScatterList<'_>>,
        assoclen: u32,
        cryptlen: u32,
        key: Pin<&[u8]>,
        iv: Pin<&mut [u8]>,
    ) -> Result {
        let _lock = self.lock.lock();
        self.set_key(key)?;
        self.set_crypt(src, dst, assoclen, cryptlen, iv);
        // SAFETY: `request` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err = bindings::crypto_aead_encrypt(self.request);
            to_result(err)
        }
    }

    /// Decrypt ciphertext.
    ///
    /// `src`: source data scatterlist, holds the `assoc data || ciphertext || auth tag`;
    /// `dst`:  destination data scatterlist, holds the `assoc data || plaintext`;
    /// `assoclen`: the length (in bytes) of `assoc data`;
    /// `cryptlen`: the length (in bytes) of `ciphertext || auth tag`;
    /// `key`: the symmetric key, used for the cipher operation;
    /// `iv`: the Initialization Vector for the cipher operation, may be modified.
    ///
    /// Returns `Ok(())` if the cipher operation was successful, or an error code in [`Error`].
    pub fn decrypt(
        &self,
        src: Pin<&ScatterList<'_>>,
        dst: Pin<&mut ScatterList<'_>>,
        assoclen: u32,
        cryptlen: u32,
        key: Pin<&[u8]>,
        iv: Pin<&mut [u8]>,
    ) -> Result {
        let _lock = self.lock.lock();
        self.set_key(key)?;
        self.set_crypt(src, dst, assoclen, cryptlen, iv);
        // SAFETY: `request` is constructed by the `new` constructor, so it's valid.
        unsafe {
            let err = bindings::crypto_aead_decrypt(self.request);
            to_result(err)
        }
    }
}

#[pinned_drop]
impl PinnedDrop for Cipher {
    fn drop(self: Pin<&mut Self>) {
        let aead = self.as_ref().get_ref().aead;
        let request = self.as_ref().get_ref().request;
        // SAFETY: `aead` and `request` is constructed by the `new` constructor,
        // so they are valid.
        unsafe {
            let base = addr_of_mut!((*aead).base);
            bindings::crypto_destroy_tfm(aead as *mut core::ffi::c_void, base);
            bindings::kfree_sensitive(request as *const core::ffi::c_void);
        }
    }
}