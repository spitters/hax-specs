//! Cross-check: xtsaes-hax against the RustCrypto `xts-mode` crate.
//!
//! `xts_encrypt_sector` and `xts_decrypt_sector` are compared byte for byte
//! with `xts_mode::Xts128<Aes128>` on whole-block data units of 1 to
//! `MAX_BLOCKS` blocks, over several keys and tweaks. Both directions are
//! checked (our encrypt against theirs, our decrypt of their ciphertext, and
//! their decrypt of our ciphertext), and a ciphertext with one flipped bit
//! is checked not to decrypt to the original plaintext.

use aes::cipher::generic_array::GenericArray;
use aes::cipher::KeyInit;
use aes::Aes128;
use xts_mode::Xts128;
use xtsaes_hax::{sector_number_to_tweak, xts_decrypt_sector, xts_encrypt_sector, MAX_BLOCKS};

type Blocks = [[u8; 16]; MAX_BLOCKS];

fn reference(key1: &[u8; 16], key2: &[u8; 16]) -> Xts128<Aes128> {
    let c1 = Aes128::new(GenericArray::from_slice(key1));
    let c2 = Aes128::new(GenericArray::from_slice(key2));
    Xts128::<Aes128>::new(c1, c2)
}

fn to_blocks(bytes: &[u8]) -> Blocks {
    let mut out: Blocks = [[0u8; 16]; MAX_BLOCKS];
    for (i, chunk) in bytes.chunks(16).enumerate() {
        out[i].copy_from_slice(chunk);
    }
    out
}

fn from_blocks(blocks: &Blocks, num_blocks: usize) -> Vec<u8> {
    blocks[..num_blocks].concat()
}

/// A deterministic byte pattern; distinct seeds give distinct inputs.
fn pattern(seed: u8, len: usize) -> Vec<u8> {
    (0..len)
        .map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed).wrapping_mul(seed | 1))
        .collect()
}

const KEYS: [([u8; 16], [u8; 16]); 4] = [
    ([0u8; 16], [0u8; 16]),
    ([0x11; 16], [0x22; 16]),
    (
        [0x27, 0x18, 0x28, 0x18, 0x28, 0x45, 0x90, 0x45, 0x23, 0x53, 0x60, 0x28, 0x74, 0x71, 0x35, 0x26],
        [0x31, 0x41, 0x59, 0x26, 0x53, 0x58, 0x97, 0x93, 0x23, 0x84, 0x62, 0x64, 0x33, 0x83, 0x27, 0x95],
    ),
    ([0xff; 16], [0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]),
];

const SECTORS: [u64; 5] = [0, 1, 0x3333333333, 0xffff_ffff, u64::MAX];

fn check_one(key1: &[u8; 16], key2: &[u8; 16], sector: u64, num_blocks: usize, seed: u8) {
    let xts = reference(key1, key2);
    let tweak = sector_number_to_tweak(sector);
    let pt = pattern(seed, 16 * num_blocks);

    // Our encrypt against theirs.
    let ours = xts_encrypt_sector(key1, key2, &tweak, &to_blocks(&pt), num_blocks);
    let ours_ct = from_blocks(&ours, num_blocks);
    let mut theirs_ct = pt.clone();
    xts.encrypt_sector(&mut theirs_ct, tweak);
    assert_eq!(ours_ct, theirs_ct, "encrypt: sector {sector}, {num_blocks} blocks, seed {seed}");

    // Our decrypt of their ciphertext.
    let dec = xts_decrypt_sector(key1, key2, &tweak, &to_blocks(&theirs_ct), num_blocks);
    assert_eq!(from_blocks(&dec, num_blocks), pt, "decrypt (ours of theirs): sector {sector}, {num_blocks} blocks");

    // Their decrypt of our ciphertext.
    let mut theirs_pt = ours_ct.clone();
    xts.decrypt_sector(&mut theirs_pt, tweak);
    assert_eq!(theirs_pt, pt, "decrypt (theirs of ours): sector {sector}, {num_blocks} blocks");

    // A flipped ciphertext bit must not decrypt to the plaintext.
    let mut tampered = ours;
    let last = num_blocks - 1;
    tampered[last][7] ^= 0x01;
    let dec_t = xts_decrypt_sector(key1, key2, &tweak, &tampered, num_blocks);
    assert_ne!(dec_t[last], to_blocks(&pt)[last], "tampered block must change on decrypt");
}

#[test]
fn crosscheck_all_lengths_single_key() {
    let (key1, key2) = KEYS[1];
    for num_blocks in 1..=MAX_BLOCKS {
        check_one(&key1, &key2, 0x3333333333, num_blocks, num_blocks as u8);
    }
}

#[test]
fn crosscheck_keys_and_sectors() {
    for (k, (key1, key2)) in KEYS.iter().enumerate() {
        for (s, &sector) in SECTORS.iter().enumerate() {
            for &num_blocks in &[1usize, 2, 3, 31, MAX_BLOCKS] {
                check_one(key1, key2, sector, num_blocks, (k * 16 + s) as u8);
            }
        }
    }
}

#[test]
fn crosscheck_edge_data() {
    let (key1, key2) = KEYS[2];
    let xts = reference(&key1, &key2);
    for fill in [0x00u8, 0xff] {
        let pt = vec![fill; 16 * MAX_BLOCKS];
        let tweak = sector_number_to_tweak(7);
        let ours = xts_encrypt_sector(&key1, &key2, &tweak, &to_blocks(&pt), MAX_BLOCKS);
        let mut theirs = pt.clone();
        xts.encrypt_sector(&mut theirs, tweak);
        assert_eq!(from_blocks(&ours, MAX_BLOCKS), theirs, "fill {fill:#04x}");
    }
}
