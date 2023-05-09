// SPDX-License-Identifier: GPL-2.0

//! Rust cipher sample.

use alloc::boxed::Box;
use kernel::crypto::{aead, skcipher};
use kernel::prelude::*;
use kernel::scatterlist::{RawScatterList, ScatterList};
use kernel::{c_str, stack_pin_init, stack_try_pin_init};

module! {
    type: RustCipher,
    name: "rust_cipher",
    author: "Rust for Linux Contributors",
    description: "Rust cipher sample",
    license: "GPL",
}

struct RustCipher;

impl RustCipher {
    fn test_aead() {
        stack_try_pin_init!(let aes_gcm = aead::Cipher::new(c_str!("gcm(aes)"), 0, 0));
        if let Err(e) = aes_gcm {
            pr_info!("alloc gcm(aes) cipher failed, errno:{},0n", e.to_errno());
            return;
        }
        let aes_gcm = aes_gcm.ok().unwrap();
        pr_info!("gcm(aes):\n");
        pr_info!("ivsize:{}\n", aes_gcm.ivsize());
        pr_info!("authsize:{}\n", aes_gcm.authsize());
        pr_info!("blocksize:{}\n", aes_gcm.blocksize());
        pr_info!("reqsize:{}\n", aes_gcm.reqsize());

        // From McGrew & Viega - http://citeseer.ist.psu.edu/656989.html
        let key: Pin<&mut [u8; 16]> = core::pin::pin!([
            0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c, 0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30,
            0x83, 0x08,
        ]);
        let mut iv: Pin<&mut [u8; 12]> = core::pin::pin!([
            0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce, 0xdb, 0xad, 0xde, 0xca, 0xf8, 0x88,
        ]);
        let mut plaintext: [u8; 64] = [
            0xd9, 0x31, 0x32, 0x25, 0xf8, 0x84, 0x06, 0xe5, 0xa5, 0x59, 0x09, 0xc5, 0xaf, 0xf5,
            0x26, 0x9a, 0x86, 0xa7, 0xa9, 0x53, 0x15, 0x34, 0xf7, 0xda, 0x2e, 0x4c, 0x30, 0x3d,
            0x8a, 0x31, 0x8a, 0x72, 0x1c, 0x3c, 0x0c, 0x95, 0x95, 0x68, 0x09, 0x53, 0x2f, 0xcf,
            0x0e, 0x24, 0x49, 0xa6, 0xb5, 0x25, 0xb1, 0x6a, 0xed, 0xf5, 0xaa, 0x0d, 0xe6, 0x57,
            0xba, 0x63, 0x7b, 0x39, 0x1a, 0xaf, 0xd2, 0x55,
        ];
        let expected_data: [u8; 64] = [
            0x42, 0x83, 0x1e, 0xc2, 0x21, 0x77, 0x74, 0x24, 0x4b, 0x72, 0x21, 0xb7, 0x84, 0xd0,
            0xd4, 0x9c, 0xe3, 0xaa, 0x21, 0x2f, 0x2c, 0x02, 0xa4, 0xe0, 0x35, 0xc1, 0x7e, 0x23,
            0x29, 0xac, 0xa1, 0x2e, 0x21, 0xd5, 0x14, 0xb2, 0x54, 0x66, 0x93, 0x1c, 0x7d, 0x8f,
            0x6a, 0x5a, 0xac, 0x84, 0xaa, 0x05, 0x1b, 0xa3, 0x0b, 0x39, 0x6a, 0x0a, 0xac, 0x97,
            0x3d, 0x58, 0xe0, 0x91, 0x47, 0x3f, 0x59, 0x85,
        ];
        let expected_mac: [u8; 16] = [
            0x4d, 0x5c, 0x2a, 0xf3, 0x27, 0xcd, 0x64, 0xa6, 0x2c, 0xf3, 0x5a, 0xbd, 0x2b, 0xa6,
            0xfa, 0xb4,
        ];

        let buf0 = Pin::new(plaintext.as_mut());
        stack_pin_init!(let src = RawScatterList::<1>::new());
        let src: Pin<&mut RawScatterList<1>> = src;
        src.set_buf(0, buf0);
        stack_pin_init!(let src = ScatterList::from_raw(src));
        let src: Pin<&mut ScatterList> = src;
        pr_info!("plaintext:{:?}\n", plaintext);

        let mut ciphertext = [0u8; 64];
        let mut mac = [0u8; 16];
        let buf0 = Pin::new(ciphertext.as_mut());
        let buf1 = Pin::new(mac.as_mut());
        stack_pin_init!(let dst = RawScatterList::<2>::new());
        let dst: Pin<&mut RawScatterList<2>> = dst;
        dst.set_buf(0, buf0);
        dst.set_buf(1, buf1);
        stack_pin_init!(let dst = ScatterList::from_raw(dst));
        let mut dst: Pin<&mut ScatterList> = dst;

        if let Err(e) =
            aes_gcm.encrypt(src.as_ref(), dst.as_mut(), 0, 64, key.as_ref(), iv.as_mut())
        {
            pr_info!("aead encrypt failed, errno:{}\n", e.to_errno());
            return;
        }
        pr_info!("ciphertext:{:?}\n", ciphertext);
        pr_info!("mac:{:?}\n", mac);
        assert_eq!(ciphertext, expected_data);
        assert_eq!(mac, expected_mac);

        let mut decrypted = [0u8; 64];
        let buf0 = Pin::new(decrypted.as_mut());
        stack_pin_init!(let ret = RawScatterList::<1>::new());
        let ret: Pin<&mut RawScatterList<1>> = ret;
        ret.set_buf(0, buf0);
        stack_pin_init!(let ret = ScatterList::from_raw(ret));
        let mut ret: Pin<&mut ScatterList> = ret;

        if let Err(e) =
            aes_gcm.decrypt(dst.as_ref(), ret.as_mut(), 0, 80, key.as_ref(), iv.as_mut())
        {
            pr_info!("aead decrypt failed, errno:{}\n", e.to_errno());
            return;
        }
        pr_info!("decrypted:{:?}\n", decrypted);
        assert_eq!(plaintext, decrypted);
    }

    fn test_skcipher() {
        let aes_cbc = Box::pin_init(skcipher::Cipher::new(c_str!("cbc(aes)"), 0, 0));
        if let Err(e) = aes_cbc {
            pr_info!("alloc cbc(aes) cipher failed, errno:{}\n", e.to_errno());
            return;
        }
        let aes_cbc = aes_cbc.ok().unwrap();
        pr_info!("cbc(aes):\n");
        pr_info!("ivsize:{}\n", aes_cbc.ivsize());
        pr_info!("blocksize:{}\n", aes_cbc.blocksize());
        pr_info!("reqsize:{}\n", aes_cbc.reqsize());

        // From RFC 3602
        let key: Pin<&mut [u8; 16]> = core::pin::pin!([
            0xc2, 0x86, 0x69, 0x6d, 0x88, 0x7c, 0x9a, 0xa0, 0x61, 0x1b, 0xbb, 0x3e, 0x20, 0x25,
            0xa4, 0x5a,
        ]);
        let mut iv: Pin<&mut [u8; 16]> = core::pin::pin!([
            0x56, 0x2e, 0x17, 0x99, 0x6d, 0x09, 0x3d, 0x28, 0xdd, 0xb3, 0xba, 0x69, 0x5a, 0x2e,
            0x6f, 0x58,
        ]);
        let iv_out: Pin<&mut [u8; 16]> = core::pin::pin!([
            0x75, 0x86, 0x60, 0x2d, 0x25, 0x3c, 0xff, 0xf9, 0x1b, 0x82, 0x66, 0xbe, 0xa6, 0xd6,
            0x1a, 0xb1,
        ]);
        let plaintext: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
            0x1c, 0x1d, 0x1e, 0x1f,
        ];
        let expected: [u8; 32] = [
            0xd2, 0x96, 0xcd, 0x94, 0xc2, 0xcc, 0xcf, 0x8a, 0x3a, 0x86, 0x30, 0x28, 0xb5, 0xe1,
            0xdc, 0x0a, 0x75, 0x86, 0x60, 0x2d, 0x25, 0x3c, 0xff, 0xf9, 0x1b, 0x82, 0x66, 0xbe,
            0xa6, 0xd6, 0x1a, 0xb1,
        ];

        let src = Box::pin_init(ScatterList::new(32));
        if let Err(e) = src {
            pr_info!("alloc src scatterlist failed, errno:{}\n", e.to_errno());
            return;
        }
        let src = src.ok().unwrap();
        src.copy_from_buffer(&plaintext, 0).ok().unwrap();
        pr_info!("plaintext:{:?}\n", plaintext);

        let dst = Box::pin_init(ScatterList::new(32));
        if let Err(e) = dst {
            pr_info!("alloc dst scatterlist failed, errno:{}\n", e.to_errno());
            return;
        }
        let mut dst = dst.ok().unwrap();

        if let Err(e) = aes_cbc.encrypt(src.as_ref(), dst.as_mut(), 32, key.as_ref(), iv.as_mut()) {
            pr_info!("skcipher encrypt failed, errno:{}\n", e.to_errno());
            return;
        }

        let mut ciphertext = [0u8; 32];
        dst.copy_to_buffer(&mut ciphertext, 0).ok().unwrap();
        pr_info!("ciphertext:{:?}\n", ciphertext);
        assert_eq!(ciphertext, expected);
        assert_eq!(iv.as_ref(), iv_out.as_ref());

        src.copy_from_buffer(&ciphertext, 0).ok().unwrap();
        let mut iv: Pin<&mut [u8; 16]> = core::pin::pin!([
            0x56, 0x2e, 0x17, 0x99, 0x6d, 0x09, 0x3d, 0x28, 0xdd, 0xb3, 0xba, 0x69, 0x5a, 0x2e,
            0x6f, 0x58,
        ]);
        if let Err(e) = aes_cbc.decrypt(src.as_ref(), dst.as_mut(), 32, key.as_ref(), iv.as_mut()) {
            pr_info!("skcipher decrypt failed, errno:{}\n", e.to_errno());
            return;
        }

        let mut decrypted = [0u8; 32];
        dst.copy_to_buffer(&mut decrypted, 0).ok().unwrap();
        pr_info!("decrypted:{:?}\n", decrypted);
        assert_eq!(plaintext, decrypted);
    }
}

impl kernel::Module for RustCipher {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        pr_info!("Rust cipher sample (init)\n");

        Self::test_aead();
        Self::test_skcipher();

        Ok(RustCipher)
    }
}

impl Drop for RustCipher {
    fn drop(&mut self) {
        pr_info!("Rust cipher sample (exit)\n");
    }
}
