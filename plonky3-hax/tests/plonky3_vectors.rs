//! Known-answer tests from the Plonky3 sources.
//!
//! Every constant below is copied byte for byte from the crate
//! `p3-baby-bear` 0.5.2 as published on crates.io (Plonky3 repository,
//! directory `baby-bear`, commit `3b3e175030dbd22770387eb9bf4f59e437fcab34`
//! according to the crate's `.cargo_vcs_info.json`). The two files cited are
//! identical in `p3-baby-bear` 0.5.3 (commit
//! `cf8b088497b87ff83cd1d80349e8bba370907c03`). The tests drive this crate's
//! own functions; no Plonky3 code runs here.
//!
//! - `src/poseidon2.rs`, test `test_default_babybear_poseidon2_width_16`
//!   (lines 469–486): one input/output pair of
//!   `default_babybear_poseidon2_16()`. The input is the output of the Sage
//!   command `set_random_seed(16); vector([BB.random_element() for t in range(16)])`
//!   quoted in the neighbouring test; the expected output is the value
//!   recorded by Plonky3.
//! - `src/baby_bear.rs`, `impl TwoAdicData for BabyBearParameters`
//!   (lines 46–62): `TWO_ADIC_GENERATORS`, `ROOTS_8`, `INV_ROOTS_8`,
//!   `ROOTS_16`, `INV_ROOTS_16`.
//! - `src/baby_bear.rs`, `impl MontyParameters` and
//!   `impl RelativelyPrimePower<7>` (lines 18, 29, 33–37): `PRIME`,
//!   `MONTY_GEN` and the exponent `1725656503` of the 7-th root map.

use plonky3_hax::specs::baby_bear::*;
use plonky3_hax::specs::poseidon2::*;

// ========================================================================
// Poseidon2, width 16
// ========================================================================

/// `p3-baby-bear` 0.5.2, `src/poseidon2.rs`, lines 470–474.
const P3_POSEIDON2_16_INPUT: [u64; 16] = [
    894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
    120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
    1783754913,
];

/// `p3-baby-bear` 0.5.2, `src/poseidon2.rs`, lines 476–480.
const P3_POSEIDON2_16_EXPECTED: [u64; 16] = [
    516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906,
    563338433, 319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758,
    1052633829, 1344246938,
];

#[test]
fn kat_poseidon2_16_plonky3_default() {
    let mut state = P3_POSEIDON2_16_INPUT;
    poseidon2_permute_16(&mut state);
    assert_eq!(state, P3_POSEIDON2_16_EXPECTED);
}

// ========================================================================
// Field parameters
// ========================================================================

/// `p3-baby-bear` 0.5.2, `src/baby_bear.rs`, lines 46–51.
const P3_TWO_ADIC_GENERATORS: [u64; 28] = [
    0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090, 0x17b56c64,
    0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a, 0x62c3d2b1,
    0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0xba067a3, 0x18adc27d,
    0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41,
];

/// `p3-baby-bear` 0.5.2, `src/baby_bear.rs`, lines 53–62.
const P3_ROOTS_8: [u64; 4] = [0x1, 0x5ee99486, 0x67055c21, 0xc9ea3ba];
const P3_INV_ROOTS_8: [u64; 4] = [0x1, 0x6b615c47, 0x10faa3e0, 0x19166b7b];
const P3_ROOTS_16: [u64; 8] = [
    0x1, 0xbb4c4e4, 0x5ee99486, 0x4b49e08, 0x67055c21, 0x5376917a, 0xc9ea3ba, 0x563112a7,
];
const P3_INV_ROOTS_16: [u64; 8] = [
    0x1, 0x21ceed5a, 0x6b615c47, 0x24896e87, 0x10faa3e0, 0x734b61f9, 0x19166b7b, 0x6c4b3b1d,
];

#[test]
fn kat_prime_and_generator() {
    // `const PRIME: u32 = 0x78000001;` and `MONTY_GEN = BabyBear::new(31)`.
    assert_eq!(BABY_BEAR_PRIME, 0x78000001);
    assert_eq!(GENERATOR, 31);
}

#[test]
fn kat_two_adic_generators() {
    for k in 0..28u32 {
        assert_eq!(bb_root_of_unity(k), P3_TWO_ADIC_GENERATORS[k as usize], "k = {}", k);
    }
}

#[test]
fn kat_roots_8_and_16() {
    let w8 = bb_root_of_unity(3);
    let w16 = bb_root_of_unity(4);
    for i in 0..4 {
        assert_eq!(bb_pow(w8, i as u64), P3_ROOTS_8[i], "ROOTS_8[{}]", i);
        assert_eq!(bb_inv(P3_ROOTS_8[i]), P3_INV_ROOTS_8[i], "INV_ROOTS_8[{}]", i);
    }
    for i in 0..8 {
        assert_eq!(bb_pow(w16, i as u64), P3_ROOTS_16[i], "ROOTS_16[{}]", i);
        assert_eq!(bb_inv(P3_ROOTS_16[i]), P3_INV_ROOTS_16[i], "INV_ROOTS_16[{}]", i);
    }
}

#[test]
fn kat_seventh_root_exponent() {
    // `a^{1/7}` is `a^1725656503`, since `7 * 1725656503 = 1 mod (p - 1)`.
    const ROOT_7_EXP: u64 = 1725656503;
    assert_eq!((7 * ROOT_7_EXP) % (BABY_BEAR_PRIME - 1), 1);
    for &x in &[0u64, 1, 2, 7, 31, 0x5ee99486, BABY_BEAR_PRIME - 1] {
        assert_eq!(bb_pow(bb_pow(x, 7), ROOT_7_EXP), x, "x = {}", x);
        assert_eq!(bb_pow(bb_pow(x, ROOT_7_EXP), 7), x, "x = {}", x);
    }
}
