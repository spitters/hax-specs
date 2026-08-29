//! Byte-exact Known-Answer Tests for AES-128/256-GCM.
//!
//! These exercise the AES (FIPS 197) + GHASH (GF(2^128)) primitives
//! in `aesgcm_hax` against:
//!
//!   1. NIST CAVP GCMVS test vectors (`gcmEncryptExtIV{128,256}.rsp`,
//!      dated 2012-08-31), byte-for-byte on (CT, Tag); and
//!   2. The RustCrypto `aes-gcm` v0.10.3 crate (NIST-validated) on the same
//!      inputs, asserting equality of `ciphertext || tag`.
//!
//! The structural property tests (roundtrip, tamper detection, determinism,
//! key/nonce sensitivity) run against the `RealGcm` backend.

use aesgcm_hax::aes_impl::{aes128_encrypt_block, aes256_encrypt_block};
use aesgcm_hax::counter::{gctr_one_block, inc32, xor_blocks};
use aesgcm_hax::gcm::{gcm_decrypt, gcm_encrypt, zero_block};
use aesgcm_hax::realgcm::{gcm_decrypt_var, gcm_encrypt_var, AesVariant, RealGcm};
use aesgcm_hax::types::{AesBlock, AesKey, GcmNonce, GcmTag};

use aes_gcm::aead::{AeadInPlace, KeyInit};
use aes_gcm::{Aes128Gcm, Aes256Gcm, Nonce};

// ---------------------------------------------------------------------------
// hex helpers (test-only; std is available in the test harness)
// ---------------------------------------------------------------------------

fn hex(s: &str) -> Vec<u8> {
    let s = s.trim();
    assert!(s.len().is_multiple_of(2), "odd hex length");
    let mut out = Vec::with_capacity(s.len() / 2);
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let hi = (b[i] as char).to_digit(16).expect("hex") as u8;
        let lo = (b[i + 1] as char).to_digit(16).expect("hex") as u8;
        out.push((hi << 4) | lo);
        i += 2;
    }
    out
}

fn key32(bytes: &[u8]) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[..bytes.len()].copy_from_slice(bytes);
    k
}

fn nonce12(bytes: &[u8]) -> GcmNonce {
    let mut n = [0u8; 12];
    n.copy_from_slice(bytes);
    n
}

fn tag16(bytes: &[u8]) -> GcmTag {
    let mut t = [0u8; 16];
    t.copy_from_slice(bytes);
    t
}

// ===========================================================================
// A. Raw AES block KATs (FIPS 197 Appendix C.1 / C.3)
// ===========================================================================

#[test]
fn aes128_fips197_c1() {
    // FIPS 197 C.1: key 000102...0f, input 00112233...ff -> 69c4e0d86a7b0430d8cdb78070b4c55a
    let key: AesKey = hex("000102030405060708090a0b0c0d0e0f").try_into().unwrap();
    let input: AesBlock = hex("00112233445566778899aabbccddeeff").try_into().unwrap();
    let expected: AesBlock = hex("69c4e0d86a7b0430d8cdb78070b4c55a").try_into().unwrap();
    assert_eq!(aes128_encrypt_block(&key, &input), expected);
}

#[test]
fn aes256_fips197_c3() {
    // FIPS 197 C.3: key 000102...1f, input 00112233...ff -> 8ea2b7ca516745bfeafc49904b496089
    let key: [u8; 32] = hex("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
        .try_into()
        .unwrap();
    let input: AesBlock = hex("00112233445566778899aabbccddeeff").try_into().unwrap();
    let expected: AesBlock = hex("8ea2b7ca516745bfeafc49904b496089").try_into().unwrap();
    assert_eq!(aes256_encrypt_block(&key, &input), expected);
}

// ===========================================================================
// B. NIST CAVP GCMVS byte-exact KATs (gcmEncryptExtIV*.rsp, Count = 0)
// ===========================================================================

/// Run one NIST vector through the variable-length core and assert
/// byte-exact (CT, Tag), then confirm decrypt-verify round-trips.
fn check_nist_vector(
    variant: AesVariant,
    key_hex: &str,
    iv_hex: &str,
    pt_hex: &str,
    aad_hex: &str,
    ct_hex: &str,
    tag_hex: &str,
) {
    let key = key32(&hex(key_hex));
    let nonce = nonce12(&hex(iv_hex));
    let pt = hex(pt_hex);
    let aad = hex(aad_hex);
    let exp_ct = hex(ct_hex);
    let exp_tag = tag16(&hex(tag_hex));

    let mut ct = vec![0u8; pt.len()];
    let tag = gcm_encrypt_var(variant, &key, &nonce, &aad, &pt, &mut ct);

    assert_eq!(ct, exp_ct, "ciphertext mismatch vs NIST vector");
    assert_eq!(tag, exp_tag, "tag mismatch vs NIST vector");

    // Decrypt-verify recovers the plaintext.
    let mut rec = vec![0u8; ct.len()];
    let ok = gcm_decrypt_var(variant, &key, &nonce, &aad, &ct, &tag, &mut rec);
    assert!(ok, "tag verification failed on our own ciphertext");
    assert_eq!(rec, pt, "decryption did not recover plaintext");
}

#[test]
fn nist_aes128_gcm_count0_pt128_aad128() {
    // gcmEncryptExtIV128.rsp [Keylen=128][IVlen=96][PTlen=128][AADlen=128][Taglen=128] Count=0
    check_nist_vector(
        AesVariant::Aes128,
        "c939cc13397c1d37de6ae0e1cb7c423c",
        "b3d8cc017cbb89b39e0f67e2",
        "c3b3c41f113a31b73d9a5cd432103069",
        "24825602bd12a984e0092d3e448eda5f",
        "93fe7d9e9bfd10348a5606e5cafa7354",
        "0032a1dc85f1c9786925a2e71d8272dd",
    );
}

#[test]
fn nist_aes128_gcm_count0_pt256_aad128() {
    // gcmEncryptExtIV128.rsp [PTlen=256][AADlen=128][Taglen=128] Count=0 (2 ciphertext blocks)
    check_nist_vector(
        AesVariant::Aes128,
        "298efa1ccf29cf62ae6824bfc19557fc",
        "6f58a93fe1d207fae4ed2f6d",
        "cc38bccd6bc536ad919b1395f5d63801f99f8068d65ca5ac63872daf16b93901",
        "021fafd238463973ffe80256e5b1c6b1",
        "dfce4e9cd291103d7fe4e63351d9e79d3dfd391e3267104658212da96521b7db",
        "542465ef599316f73a7a560509a2d9f2",
    );
}

#[test]
fn nist_aes128_gcm_count0_pt128_aad0() {
    // gcmEncryptExtIV128.rsp [PTlen=128][AADlen=0][Taglen=128] Count=0 (empty AAD)
    check_nist_vector(
        AesVariant::Aes128,
        "7fddb57453c241d03efbed3ac44e371c",
        "ee283a3fc75575e33efd4887",
        "d5de42b461646c255c87bd2962d3b9a2",
        "",
        "2ccda4a5415cb91e135c2a0f78c9b2fd",
        "b36d1df9b9d5e596f83e8b7f52971cb3",
    );
}

#[test]
fn nist_aes256_gcm_count0_pt128_aad128() {
    // gcmEncryptExtIV256.rsp [Keylen=256][IVlen=96][PTlen=128][AADlen=128][Taglen=128] Count=0
    check_nist_vector(
        AesVariant::Aes256,
        "92e11dcdaa866f5ce790fd24501f92509aacf4cb8b1339d50c9c1240935dd08b",
        "ac93a1a6145299bde902f21a",
        "2d71bcfa914e4ac045b2aa60955fad24",
        "1e0889016f67601c8ebea4943bc23ad6",
        "8995ae2e6df3dbf96fac7b7137bae67f",
        "eca5aa77d51d4a0a14d9c51e1da474ab",
    );
}

// ===========================================================================
// C. Differential cross-check against the RustCrypto `aes-gcm` crate
// ===========================================================================

fn crate_aes128(key: &[u8; 16], nonce: &[u8; 12], aad: &[u8], pt: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let cipher = Aes128Gcm::new(key.into());
    let mut buf = pt.to_vec();
    let tag = cipher
        .encrypt_in_place_detached(Nonce::from_slice(nonce), aad, &mut buf)
        .expect("aes-gcm encrypt");
    (buf, tag.into())
}

fn crate_aes256(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], pt: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let cipher = Aes256Gcm::new(key.into());
    let mut buf = pt.to_vec();
    let tag = cipher
        .encrypt_in_place_detached(Nonce::from_slice(nonce), aad, &mut buf)
        .expect("aes-gcm encrypt");
    (buf, tag.into())
}

/// Compare our (ct||tag) to the crate's, byte-for-byte, over several
/// input shapes (block-aligned and partial-block plaintext/AAD).
#[test]
fn crosscheck_aes128_vs_crate() {
    let key: [u8; 16] = hex("feffe9928665731c6d6a8f9467308308").try_into().unwrap();
    let nonce: [u8; 12] = hex("cafebabefacedbaddecaf888").try_into().unwrap();

    let cases: &[(&str, &str)] = &[
        // (plaintext_hex, aad_hex)
        ("", ""),
        ("00", ""),
        ("00112233445566778899aabbccddeeff", ""),
        ("00112233445566778899aabbccddeeff", "0123456789"),
        (
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
            "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        ),
    ];

    for (pt_hex, aad_hex) in cases {
        let pt = hex(pt_hex);
        let aad = hex(aad_hex);

        let (crate_ct, crate_tag) = crate_aes128(&key, &nonce, &aad, &pt);

        let mut ct = vec![0u8; pt.len()];
        let tag = gcm_encrypt_var(
            AesVariant::Aes128,
            &key32(&key),
            &nonce12(&nonce),
            &aad,
            &pt,
            &mut ct,
        );

        assert_eq!(ct, crate_ct, "ct mismatch vs aes-gcm crate (pt={pt_hex})");
        assert_eq!(tag, crate_tag, "tag mismatch vs aes-gcm crate (pt={pt_hex})");
    }
}

#[test]
fn crosscheck_aes256_vs_crate() {
    let key: [u8; 32] =
        hex("feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308")
            .try_into()
            .unwrap();
    let nonce: [u8; 12] = hex("cafebabefacedbaddecaf888").try_into().unwrap();

    let cases: &[(&str, &str)] = &[
        ("", ""),
        ("2d71bcfa914e4ac045b2aa60955fad24", "1e0889016f67601c8ebea4943bc23ad6"),
        (
            "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
            "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        ),
    ];

    for (pt_hex, aad_hex) in cases {
        let pt = hex(pt_hex);
        let aad = hex(aad_hex);

        let (crate_ct, crate_tag) = crate_aes256(&key, &nonce, &aad, &pt);

        let mut ct = vec![0u8; pt.len()];
        let tag = gcm_encrypt_var(
            AesVariant::Aes256,
            &key,
            &nonce12(&nonce),
            &aad,
            &pt,
            &mut ct,
        );

        assert_eq!(ct, crate_ct, "ct mismatch vs aes-gcm crate (pt={pt_hex})");
        assert_eq!(tag, crate_tag, "tag mismatch vs aes-gcm crate (pt={pt_hex})");
    }
}

// ===========================================================================
// D. Cross-check the fixed-shape gcm::gcm_encrypt (64-byte PT, 16-byte AAD)
//    backed by RealGcm against the aes-gcm crate.
// ===========================================================================

const TEST_KEY: AesKey = [
    0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
];
const TEST_NONCE: GcmNonce = [0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB];
const TEST_AAD: AesBlock = [
    0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF,
];
const TEST_PT: [u8; 64] = [
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,
];

#[test]
fn fixed_shape_gcm_matches_crate() {
    let (ct, tag) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);

    let (crate_ct, crate_tag) = crate_aes128(&TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);

    assert_eq!(&ct[..], &crate_ct[..], "fixed-shape ct mismatch vs aes-gcm crate");
    assert_eq!(&tag[..], &crate_tag[..], "fixed-shape tag mismatch vs aes-gcm crate");
}

// ===========================================================================
// E. Structural property tests over the RealGcm backend
// ===========================================================================

#[test]
fn encrypt_decrypt_roundtrip() {
    let (ct, tag) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    assert_ne!(ct, TEST_PT, "ciphertext must differ from plaintext");
    let recovered = gcm_decrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &ct, &tag);
    assert!(recovered.is_some(), "decryption must succeed");
    assert_eq!(recovered.unwrap(), TEST_PT);
}

#[test]
fn encrypt_determinism() {
    let (ct1, tag1) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    let (ct2, tag2) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    assert_eq!(ct1, ct2);
    assert_eq!(tag1, tag2);
}

#[test]
fn different_key_different_ciphertext() {
    let key2: AesKey = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0,
        0x00,
    ];
    let (ct1, _) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    let (ct2, _) = gcm_encrypt(RealGcm, &key2, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    assert_ne!(ct1, ct2);
}

#[test]
fn different_nonce_different_ciphertext() {
    let nonce2: GcmNonce = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B,
    ];
    let (ct1, _) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    let (ct2, _) = gcm_encrypt(RealGcm, &TEST_KEY, &nonce2, &TEST_AAD, &TEST_PT);
    assert_ne!(ct1, ct2);
}

#[test]
fn tampered_ciphertext_fails() {
    let (mut ct, tag) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    ct[0] ^= 0x01;
    assert!(gcm_decrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &ct, &tag).is_none());
}

#[test]
fn tampered_tag_fails() {
    let (ct, mut tag) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    tag[0] ^= 0x01;
    assert!(gcm_decrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &ct, &tag).is_none());
}

#[test]
fn wrong_aad_fails() {
    let (ct, tag) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    let wrong_aad: AesBlock = [0x00; 16];
    assert!(gcm_decrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &wrong_aad, &ct, &tag).is_none());
}

#[test]
fn wrong_key_fails() {
    let (ct, tag) = gcm_encrypt(RealGcm, &TEST_KEY, &TEST_NONCE, &TEST_AAD, &TEST_PT);
    let wrong_key: AesKey = [0xFF; 16];
    assert!(gcm_decrypt(RealGcm, &wrong_key, &TEST_NONCE, &TEST_AAD, &ct, &tag).is_none());
}

// ===========================================================================
// F. Primitive helper tests (counter / xor) retained from the suite
// ===========================================================================

#[test]
fn xor_blocks_self_cancel() {
    let a: AesBlock = [
        0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88,
    ];
    assert_eq!(xor_blocks(&a, &a), [0u8; 16]);
}

#[test]
fn inc32_carry() {
    let block: AesBlock = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xFF,
    ];
    let result = inc32(&block);
    assert_eq!(&result[12..], &[0x00, 0x00, 0x01, 0x00]);
}

#[test]
fn gctr_one_block_uses_real_aes() {
    let key: AesKey = [0x00; 16];
    let counter: AesBlock = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0,
        0x00,
    ];
    let input: AesBlock = [0xFF; 16];
    let ks = aes128_encrypt_block(&key, &counter);
    let expected = xor_blocks(&input, &ks);
    assert_eq!(gctr_one_block(RealGcm, &key, &counter, &input), expected);
}

#[test]
fn h_is_aes_zero_block() {
    // H = AES_K(0^128) (NIST SP 800-38D, Section 7.1, step 1).
    let zero: AesBlock = zero_block();
    let h = aes128_encrypt_block(&TEST_KEY, &zero);
    let crate_h = aes128_encrypt_block(&TEST_KEY, &[0u8; 16]);
    assert_eq!(h, crate_h);
    // Sanity: H is not a trivial transform of the key.
    assert_ne!(h, TEST_KEY);
}
