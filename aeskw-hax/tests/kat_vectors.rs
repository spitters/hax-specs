//! Known Answer Tests for AES Key Wrap (RFC 3394).
//!
//! Test vectors from RFC 3394, Section 4 (AES-128 KEK only).
//! These duplicate the inline tests in lib.rs but serve as integration tests
//! validating the public API independently.

use aeskw_hax::*;
use hex_literal::hex;

// ============================================================
// RFC 3394 Section 4.1: 128-bit KEK, 128-bit Key Data
// KEK  = 000102030405060708090A0B0C0D0E0F
// Data = 00112233445566778899AABBCCDDEEFF
// ============================================================

const TEST_KEK: AesKey = hex!("000102030405060708090A0B0C0D0E0F");

#[test]
fn kat_rfc3394_4_1_wrap() {
    let key_data: [u8; 16] = hex!("00112233445566778899AABBCCDDEEFF");
    let expected: [u8; 24] = hex!("1FA68B0A8112B447AEF34BD8FB5A7B829D3E862371D2CFE5");

    let wrapped = aes_wrap_128(&TEST_KEK, &key_data);
    assert_eq!(wrapped, expected, "RFC 3394 4.1 wrap");
}

#[test]
fn kat_rfc3394_4_1_unwrap() {
    let wrapped: [u8; 24] = hex!("1FA68B0A8112B447AEF34BD8FB5A7B829D3E862371D2CFE5");
    let expected: [u8; 16] = hex!("00112233445566778899AABBCCDDEEFF");

    let result = aes_unwrap_128(&TEST_KEK, &wrapped);
    assert!(result.is_some(), "RFC 3394 4.1 unwrap integrity check");
    assert_eq!(result.unwrap(), expected, "RFC 3394 4.1 unwrap data");
}

// ============================================================
// AES-128 encrypt/decrypt KAT (FIPS 197 Appendix B)
// ============================================================

#[test]
fn kat_aes128_fips197() {
    let key: AesKey = hex!("2b7e151628aed2a6abf7158809cf4f3c");
    let pt: Block = hex!("3243f6a8885a308d313198a2e0370734");
    let expected: Block = hex!("3925841d02dc09fbdc118597196a0b32");

    let ct = aes128_encrypt(&key, &pt);
    assert_eq!(ct, expected, "AES-128 encrypt");

    let recovered = aes128_decrypt(&key, &ct);
    assert_eq!(recovered, pt, "AES-128 decrypt");
}

// ============================================================
// Wrap/unwrap roundtrip tests — various key sizes
// ============================================================

#[test]
fn kat_roundtrip_128() {
    let kek: AesKey = hex!("2b7e151628aed2a6abf7158809cf4f3c");
    let key_data: [u8; 16] = hex!("deadbeefcafebabe0123456789abcdef");

    let wrapped = aes_wrap_128(&kek, &key_data);
    let unwrapped = aes_unwrap_128(&kek, &wrapped);
    assert!(unwrapped.is_some(), "128-bit roundtrip success");
    assert_eq!(unwrapped.unwrap(), key_data, "128-bit roundtrip data");
}

#[test]
fn kat_roundtrip_256() {
    let kek: AesKey = hex!("000102030405060708090a0b0c0d0e0f");
    let key_data: [u8; 32] = hex!(
        "00112233445566778899aabbccddeeff"
        "fedcba98765432100123456789abcdef"
    );

    let wrapped = aes_wrap_256(&kek, &key_data);
    let unwrapped = aes_unwrap_256(&kek, &wrapped);
    assert!(unwrapped.is_some(), "256-bit roundtrip success");
    assert_eq!(unwrapped.unwrap(), key_data, "256-bit roundtrip data");
}

#[test]
fn kat_roundtrip_192_generic() {
    // 192-bit key = 3 x 64-bit blocks, using generic interface
    let kek: AesKey = hex!("2b7e151628aed2a6abf7158809cf4f3c");
    let mut key_data: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];
    key_data[0] = hex!("0102030405060708");
    key_data[1] = hex!("090A0B0C0D0E0F10");
    key_data[2] = hex!("1112131415161718");

    let (a, r) = aes_wrap(&kek, &key_data, 3);
    let result = aes_unwrap(&kek, &a, &r, 3);
    assert!(result.is_some(), "192-bit generic roundtrip");
    let unwrapped = result.unwrap();
    for i in 0..3 {
        assert_eq!(unwrapped[i], key_data[i], "192-bit block {}", i);
    }
}

// ============================================================
// Integrity check failure tests
// ============================================================

#[test]
fn kat_unwrap_tampered() {
    let key_data: [u8; 16] = hex!("00112233445566778899AABBCCDDEEFF");
    let mut wrapped = aes_wrap_128(&TEST_KEK, &key_data);

    // Tamper with a byte in the ciphertext
    wrapped[15] ^= 0x01;
    let result = aes_unwrap_128(&TEST_KEK, &wrapped);
    assert!(result.is_none(), "Tampered ciphertext should fail");
}

#[test]
fn kat_unwrap_wrong_kek() {
    let key_data: [u8; 16] = hex!("00112233445566778899AABBCCDDEEFF");
    let wrapped = aes_wrap_128(&TEST_KEK, &key_data);

    let wrong_kek: AesKey = hex!("FF0102030405060708090A0B0C0D0E0F");
    let result = aes_unwrap_128(&wrong_kek, &wrapped);
    assert!(result.is_none(), "Wrong KEK should fail");
}

#[test]
fn kat_unwrap_tampered_iv_bytes() {
    let key_data: [u8; 16] = hex!("00112233445566778899AABBCCDDEEFF");
    let mut wrapped = aes_wrap_128(&TEST_KEK, &key_data);

    // Tamper with the first byte (part of the integrity check)
    wrapped[0] ^= 0x01;
    let result = aes_unwrap_128(&TEST_KEK, &wrapped);
    assert!(result.is_none(), "Tampered IV bytes should fail");
}

// ============================================================
// IV check
// ============================================================

#[test]
fn kat_iv_check_valid() {
    assert!(iv_check(&DEFAULT_IV));
}

#[test]
fn kat_iv_check_invalid() {
    let bad: HalfBlock = [0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0x00];
    assert!(!iv_check(&bad));
}

// ============================================================
// Half-block operations
// ============================================================

#[test]
fn kat_xor_half_involution() {
    let a: HalfBlock = hex!("0123456789abcdef");
    let b: HalfBlock = hex!("fedcba9876543210");
    let c = xor_half(&a, &b);
    let recovered = xor_half(&c, &b);
    assert_eq!(recovered, a, "XOR is involutory");
}

#[test]
fn kat_concat_split_roundtrip() {
    let left: HalfBlock = hex!("0102030405060708");
    let right: HalfBlock = hex!("090A0B0C0D0E0F10");
    let block = concat_halves(&left, &right);
    assert_eq!(msb64(&block), left, "MSB matches left");
    assert_eq!(lsb64(&block), right, "LSB matches right");
}

// ============================================================
// All-zeros and all-ones key data roundtrip
// ============================================================

#[test]
fn kat_roundtrip_all_zeros() {
    let kek: AesKey = hex!("000102030405060708090a0b0c0d0e0f");
    let key_data: [u8; 16] = [0x00; 16];

    let wrapped = aes_wrap_128(&kek, &key_data);
    let unwrapped = aes_unwrap_128(&kek, &wrapped);
    assert!(unwrapped.is_some(), "All-zeros roundtrip");
    assert_eq!(unwrapped.unwrap(), key_data);
}

#[test]
fn kat_roundtrip_all_ones() {
    let kek: AesKey = hex!("000102030405060708090a0b0c0d0e0f");
    let key_data: [u8; 16] = [0xFF; 16];

    let wrapped = aes_wrap_128(&kek, &key_data);
    let unwrapped = aes_unwrap_128(&kek, &wrapped);
    assert!(unwrapped.is_some(), "All-ones roundtrip");
    assert_eq!(unwrapped.unwrap(), key_data);
}
