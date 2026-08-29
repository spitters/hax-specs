//! Known-answer tests for the crate's own KMAC over the ported Keccak sponge.
//!
//! The Keccak self-checks use FIPS-202 published digests. The KMAC checks use
//! the NIST SP 800-185 KMAC sample vectors (KMAC_samples): Samples #1–#3 are
//! KMAC128, Samples #4–#6 are KMAC256. Every expected value below is the exact
//! published "Outval" for that sample.

use kmac_hax::{kmac128, kmac256};
use kmac_hax::keccak::{sha3_256, shake256};

/// Parse a whitespace-separated hex string into bytes.
fn hex(s: &str) -> Vec<u8> {
    let cleaned: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(cleaned.len().is_multiple_of(2), "odd hex length");
    (0..cleaned.len() / 2)
        .map(|i| u8::from_str_radix(&cleaned[2 * i..2 * i + 2], 16).unwrap())
        .collect()
}

/// SP 800-185 key: 0x40, 0x41, ..., 0x5F (32 bytes).
fn key() -> Vec<u8> {
    (0x40u8..=0x5Fu8).collect()
}

/// SP 800-185 short data: 00 01 02 03.
fn data_short() -> Vec<u8> {
    vec![0x00, 0x01, 0x02, 0x03]
}

/// SP 800-185 long data: 0x00, 0x01, ..., 0xC7 (200 bytes).
fn data_long() -> Vec<u8> {
    (0x00u8..=0xC7u8).collect()
}

// --- Keccak self-checks (FIPS-202) -----------------------------------------

#[test]
fn keccak_sha3_256_abc() {
    assert_eq!(
        sha3_256(b"abc").to_vec(),
        hex("3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe2451143153 2")
    );
}

#[test]
fn keccak_shake256_empty_prefix() {
    let mut out = [0u8; 32];
    shake256(&[], &mut out);
    assert_eq!(
        out.to_vec(),
        hex("46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f")
    );
}

// --- KMAC128 (SP 800-185 Samples #1–#3) ------------------------------------

#[test]
fn kmac128_sample1() {
    // Key = 40..5F, Data = 00 01 02 03, L = 256, S = "".
    let mut out = [0u8; 32];
    kmac128(&key(), &data_short(), &mut out, b"");
    assert_eq!(
        out.to_vec(),
        hex(
            "E5 78 0B 0D 3E A6 F7 D3 A4 29 C5 70 6A A4 3A 00
             FA DB D7 D4 96 28 83 9E 31 87 24 3F 45 6E E1 4E"
        )
    );
}

#[test]
fn kmac128_sample2() {
    // Key = 40..5F, Data = 00 01 02 03, L = 256, S = "My Tagged Application".
    let mut out = [0u8; 32];
    kmac128(&key(), &data_short(), &mut out, b"My Tagged Application");
    assert_eq!(
        out.to_vec(),
        hex(
            "3B 1F BA 96 3C D8 B0 B5 9E 8C 1A 6D 71 88 8B 71
             43 65 1A F8 BA 0A 70 70 C0 97 9E 28 11 32 4A A5"
        )
    );
}

#[test]
fn kmac128_sample3() {
    // Key = 40..5F, Data = 00..C7 (200 bytes), L = 256, S = "My Tagged Application".
    let mut out = [0u8; 32];
    kmac128(&key(), &data_long(), &mut out, b"My Tagged Application");
    assert_eq!(
        out.to_vec(),
        hex(
            "1F 5B 4E 6C CA 02 20 9E 0D CB 5C A6 35 B8 9A 15
             E2 71 EC C7 60 07 1D FD 80 5F AA 38 F9 72 92 30"
        )
    );
}

// --- KMAC256 (SP 800-185 Samples #4–#6) ------------------------------------

#[test]
fn kmac256_sample4() {
    // Key = 40..5F, Data = 00 01 02 03, L = 512, S = "My Tagged Application".
    let mut out = [0u8; 64];
    kmac256(&key(), &data_short(), &mut out, b"My Tagged Application");
    assert_eq!(
        out.to_vec(),
        hex(
            "20 C5 70 C3 13 46 F7 03 C9 AC 36 C6 1C 03 CB 64
             C3 97 0D 0C FC 78 7E 9B 79 59 9D 27 3A 68 D2 F7
             F6 9D 4C C3 DE 9D 10 4A 35 16 89 F2 7C F6 F5 95
             1F 01 03 F3 3F 4F 24 87 10 24 D9 C2 77 73 A8 DD"
        )
    );
}

#[test]
fn kmac256_sample5() {
    // Key = 40..5F, Data = 00..C7 (200 bytes), L = 512, S = "".
    let mut out = [0u8; 64];
    kmac256(&key(), &data_long(), &mut out, b"");
    assert_eq!(
        out.to_vec(),
        hex(
            "75 35 8C F3 9E 41 49 4E 94 97 07 92 7C EE 0A F2
             0A 3F F5 53 90 4C 86 B0 8F 21 CC 41 4B CF D6 91
             58 9D 27 CF 5E 15 36 9C BB FF 8B 9A 4C 2E B1 78
             00 85 5D 02 35 FF 63 5D A8 25 33 EC 6B 75 9B 69"
        )
    );
}

#[test]
fn kmac256_sample6() {
    // Key = 40..5F, Data = 00..C7 (200 bytes), L = 512, S = "My Tagged Application".
    let mut out = [0u8; 64];
    kmac256(&key(), &data_long(), &mut out, b"My Tagged Application");
    assert_eq!(
        out.to_vec(),
        hex(
            "B5 86 18 F7 1F 92 E1 D5 6C 1B 8C 55 DD D7 CD 18
             8B 97 B4 CA 4D 99 83 1E B2 69 9A 83 7D A2 E4 D9
             70 FB AC FD E5 00 33 AE A5 85 F1 A2 70 85 10 C3
             2D 07 88 08 01 BD 18 28 98 FE 47 68 76 FC 89 65"
        )
    );
}
