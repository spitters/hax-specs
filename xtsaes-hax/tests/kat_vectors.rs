//! Known Answer Tests for XTS-AES-128 (IEEE Std 1619-2018).
//!
//! Test vectors from IEEE Std 1619-2018, Annex B (AES-128); they are unchanged
//! from the 2007 edition. The tests exercise the public API from outside the
//! crate.

// The index-loop, fixed-array style mirrors the crate under test.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

use hex_literal::hex;
use xtsaes_hax::*;

// ============================================================
// IEEE 1619 Vector 1:
//   Key1 = 00000000000000000000000000000000
//   Key2 = 00000000000000000000000000000000
//   Data Unit Sequence Number = 0
//   PTX = 0000...0000 (32 bytes)
//   CTX = 917cf69ebd68b2ec9b9fe9a3eadda692
//         cd43d2f59598ed858c02c2652fbf922e
// ============================================================

#[test]
fn kat_ieee1619_vector1() {
    let key1: AesKey = [0u8; 16];
    let key2: AesKey = [0u8; 16];
    let tweak = sector_number_to_tweak(0);

    let pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 2);

    let expected_ct = hex!(
        "917cf69ebd68b2ec9b9fe9a3eadda692"
        "cd43d2f59598ed858c02c2652fbf922e"
    );

    let mut ct_flat = [0u8; 32];
    for i in 0..16 { ct_flat[i] = ct[0][i]; }
    for i in 0..16 { ct_flat[16 + i] = ct[1][i]; }
    assert_eq!(ct_flat, expected_ct, "IEEE 1619 Vector 1");
}

// ============================================================
// IEEE 1619 Vector 2:
//   Key1 = 11111111111111111111111111111111
//   Key2 = 22222222222222222222222222222222
//   Data Unit Sequence Number = 0x3333333333
//     (tweak = 33333333330000000000000000000000 in LE)
//   PTX = 44444444...44444444 (32 bytes)
//   CTX = c454185e6a16936e39334038acef838b
//         fb186fff7480adc4289382ecd6d394f0
// ============================================================

#[test]
fn kat_ieee1619_vector2() {
    let key1: AesKey = [0x11u8; 16];
    let key2: AesKey = [0x22u8; 16];
    let tweak: Block = hex!("33333333330000000000000000000000");

    let mut pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    pt[0] = [0x44u8; 16];
    pt[1] = [0x44u8; 16];

    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 2);

    let expected_ct = hex!(
        "c454185e6a16936e39334038acef838b"
        "fb186fff7480adc4289382ecd6d394f0"
    );

    let mut ct_flat = [0u8; 32];
    for i in 0..16 { ct_flat[i] = ct[0][i]; }
    for i in 0..16 { ct_flat[16 + i] = ct[1][i]; }
    assert_eq!(ct_flat, expected_ct, "IEEE 1619 Vector 2");
}

// ============================================================
// IEEE 1619 Vector 3:
//   Key1 = fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0
//   Key2 = 22222222222222222222222222222222
//   Tweak = 33333333330000000000000000000000
//   PTX = 44444444...44444444 (32 bytes)
//   CTX = af85336b597afc1a900b2eb21ec949d2
//         92df4c047e0b21532186a5971a227a89
// ============================================================

#[test]
fn kat_ieee1619_vector3() {
    let key1: AesKey = hex!("fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0");
    let key2: AesKey = [0x22u8; 16];
    let tweak: Block = hex!("33333333330000000000000000000000");

    let mut pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    pt[0] = [0x44u8; 16];
    pt[1] = [0x44u8; 16];

    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 2);

    let expected_ct = hex!(
        "af85336b597afc1a900b2eb21ec949d2"
        "92df4c047e0b21532186a5971a227a89"
    );

    let mut ct_flat = [0u8; 32];
    for i in 0..16 { ct_flat[i] = ct[0][i]; }
    for i in 0..16 { ct_flat[16 + i] = ct[1][i]; }
    assert_eq!(ct_flat, expected_ct, "IEEE 1619 Vector 3");
}

// ============================================================
// IEEE 1619 Vector 4 (512-byte / 32 blocks):
//   Key1 = 27182818284590452353602874713526
//   Key2 = 31415926535897932384626433832795
//   Tweak = 00000000000000000000000000000000
//   PTX = 000102030405...feff000102...feff (512 bytes)
//   CTX = 27a7479befa1d476...  (512 bytes)
// ============================================================

#[test]
fn kat_ieee1619_vector4() {
    let key1: AesKey = hex!("27182818284590452353602874713526");
    let key2: AesKey = hex!("31415926535897932384626433832795");
    let tweak: Block = [0u8; 16];

    // Build plaintext: repeating 0x00..0xff pattern, 512 bytes = 32 blocks
    let mut pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    for i in 0..32 {
        for j in 0..16 {
            pt[i][j] = ((i * 16 + j) % 256) as u8;
        }
    }

    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 32);

    // Expected ciphertext (first 32 bytes / 2 blocks)
    let expected_ct0: Block = hex!("27a7479befa1d476489f308cd4cfa6e2");
    let expected_ct1: Block = hex!("a96e4bbe3208ff25287dd3819616e89c");

    assert_eq!(ct[0], expected_ct0, "IEEE 1619 Vector 4, block 0");
    assert_eq!(ct[1], expected_ct1, "IEEE 1619 Vector 4, block 1");

    // Expected ciphertext last 2 blocks (blocks 30 and 31)
    let expected_ct30: Block = hex!("eb4a427d1923ce3ff262735779a418f2");
    let expected_ct31: Block = hex!("0a282df920147beabe421ee5319d0568");

    assert_eq!(ct[30], expected_ct30, "IEEE 1619 Vector 4, block 30");
    assert_eq!(ct[31], expected_ct31, "IEEE 1619 Vector 4, block 31");
}

// ============================================================
// Encrypt/decrypt roundtrip tests
// ============================================================

#[test]
fn kat_roundtrip_vector1() {
    let key1: AesKey = [0u8; 16];
    let key2: AesKey = [0u8; 16];
    let tweak = sector_number_to_tweak(0);

    let pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 2);
    let recovered = xts_decrypt_sector(&key1, &key2, &tweak, &ct, 2);

    assert_eq!(recovered[0], pt[0], "roundtrip vector 1, block 0");
    assert_eq!(recovered[1], pt[1], "roundtrip vector 1, block 1");
}

#[test]
fn kat_roundtrip_vector2() {
    let key1: AesKey = [0x11u8; 16];
    let key2: AesKey = [0x22u8; 16];
    let tweak: Block = hex!("33333333330000000000000000000000");

    let mut pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    pt[0] = [0x44u8; 16];
    pt[1] = [0x44u8; 16];

    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 2);
    let recovered = xts_decrypt_sector(&key1, &key2, &tweak, &ct, 2);

    assert_eq!(recovered[0], pt[0], "roundtrip vector 2, block 0");
    assert_eq!(recovered[1], pt[1], "roundtrip vector 2, block 1");
}

#[test]
fn kat_roundtrip_full_sector() {
    let key1: AesKey = hex!("27182818284590452353602874713526");
    let key2: AesKey = hex!("31415926535897932384626433832795");
    let tweak: Block = [0u8; 16];

    let mut pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    for i in 0..32 {
        for j in 0..16 {
            pt[i][j] = ((i * 16 + j) % 256) as u8;
        }
    }

    let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 32);
    let recovered = xts_decrypt_sector(&key1, &key2, &tweak, &ct, 32);

    for i in 0..32 {
        assert_eq!(recovered[i], pt[i], "full sector roundtrip, block {}", i);
    }
}

// ============================================================
// AES-128 known answer test (shared with lib.rs)
// ============================================================

#[test]
fn kat_aes128_fips197() {
    let key: AesKey = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
    ];
    let pt: Block = [
        0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
        0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
    ];
    let expected: Block = [
        0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb,
        0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
    ];
    assert_eq!(aes128_encrypt(&key, &pt), expected);
}

#[test]
fn kat_aes128_decrypt_roundtrip() {
    let key: AesKey = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
    ];
    let pt: Block = [
        0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
        0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
    ];
    let ct = aes128_encrypt(&key, &pt);
    let recovered = aes128_decrypt(&key, &ct);
    assert_eq!(recovered, pt, "AES-128 decrypt(encrypt(pt)) = pt");
}

// ============================================================
// GF(2^128) mul_alpha algebraic properties
// ============================================================

#[test]
fn kat_gf128_mul_alpha_zero() {
    assert_eq!(gf128_mul_alpha(&ZERO_BLOCK), ZERO_BLOCK, "alpha * 0 = 0");
}

#[test]
fn kat_gf128_mul_alpha_unit() {
    // alpha * 1 = alpha = 0x02 (in LE byte[0])
    let mut one: Block = [0u8; 16];
    one[0] = 0x01;
    let result = gf128_mul_alpha(&one);
    let mut expected: Block = [0u8; 16];
    expected[0] = 0x02;
    assert_eq!(result, expected, "alpha * 1 = 2");
}

// ============================================================
// XOR block properties
// ============================================================

#[test]
fn kat_xor_involution() {
    let a: Block = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,
        0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
    ];
    let b: Block = [
        0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
    ];
    let c = xor_block(&a, &b);
    let recovered = xor_block(&c, &b);
    assert_eq!(recovered, a, "XOR is involutory: (a ^ b) ^ b = a");
}

// ============================================================
// Sector number encoding
// ============================================================

#[test]
fn kat_sector_number_encoding() {
    // Sector 0 -> all zeros
    assert_eq!(sector_number_to_tweak(0), ZERO_BLOCK);

    // Sector 1 -> [0x01, 0, ..., 0]
    let t1 = sector_number_to_tweak(1);
    assert_eq!(t1[0], 0x01);
    for i in 1..16 {
        assert_eq!(t1[i], 0x00);
    }
}
