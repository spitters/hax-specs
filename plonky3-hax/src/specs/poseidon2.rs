//! The Poseidon2 permutation over the Baby Bear field, width 16, as
//! instantiated by `default_babybear_poseidon2_16()` in Plonky3's
//! `p3-baby-bear` 0.5 (`src/poseidon2.rs`, identical in 0.5.2 and 0.5.3).
//!
//! Round structure (Grassi, Khovratovich, Schofnegger, *Poseidon2: A Faster
//! Version of the Poseidon Hash Function*, IACR ePrint 2023/323): an initial
//! application of the external matrix `M_E`, then `R_F / 2 = 4` full rounds,
//! `R_P = 13` partial rounds and `R_F / 2 = 4` full rounds. A full round adds
//! 16 round constants, applies the S-box to every cell and multiplies by
//! `M_E`; a partial round adds one constant to `state[0]`, applies the S-box
//! to `state[0]` only and multiplies by the internal matrix `M_I`.
//!
//! Parameters:
//!
//! - S-box `x^7`; 7 is the least `d > 1` with `gcd(d, p - 1) = 1`
//!   (`BABYBEAR_S_BOX_DEGREE`).
//! - `M_4 = circ(2, 3, 1, 1)`, Plonky3's `MDSMat4`; rows `(2,3,1,1)`,
//!   `(1,2,3,1)`, `(1,1,2,3)`, `(3,1,1,2)`.
//! - `M_E = circ(2·M_4, M_4, M_4, M_4)` as a 4×4 block matrix
//!   (`mds_light_permutation` in `p3-poseidon2` 0.5).
//! - `M_I = 1 + diag(V)`, where `1` is the all-ones matrix and
//!   `V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]`
//!   (`BabyBearInternalLayerParameters::internal_layer_mat_mul`).
//! - Round constants `RC16_EXTERNAL_INITIAL`, `RC16_INTERNAL` and
//!   `RC16_EXTERNAL_FINAL` equal `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`,
//!   `BABYBEAR_POSEIDON2_RC_16_INTERNAL` and
//!   `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL` of `p3-baby-bear` 0.5.
//!
//! The HorizenLabs reference instance (`poseidon2_instance_babybear.rs`)
//! uses a different 4×4 matrix and a different internal diagonal, so it
//! computes a different permutation.

use crate::specs::baby_bear::*;

/// Permutation width.
pub const WIDTH: usize = 16;

/// Number of full rounds per half.
pub const HALF_FULL_ROUNDS: usize = 4;

/// Number of partial rounds.
pub const PARTIAL_ROUNDS: usize = 13;

/// Round constants for the 4 initial external rounds. 4×16.
pub const RC16_EXTERNAL_INITIAL: [[u64; WIDTH]; HALF_FULL_ROUNDS] = [
    [
        0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
        0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
        0x221e2e36, 0x1ab7202e,
    ],
    [
        0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
        0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
        0x52eb6ba2, 0x50642905,
    ],
    [
        0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
        0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
        0x29fbda49, 0x018afffd,
    ],
    [
        0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
        0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
        0x2cc78315, 0x1e36ea47,
    ],
];

/// Round constants for the 4 terminal external rounds. 4×16.
pub const RC16_EXTERNAL_FINAL: [[u64; WIDTH]; HALF_FULL_ROUNDS] = [
    [
        0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
        0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
        0x6a2d3d10, 0x20523767,
    ],
    [
        0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
        0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
        0x49a12590, 0x35ec52a1,
    ],
    [
        0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
        0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
        0x45e1547b, 0x4a8db2ab,
    ],
    [
        0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
        0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
        0x3c8bcd87, 0x608758b8,
    ],
];

/// Round constants for the 13 partial (internal) rounds. Applied only to `state[0]`.
pub const RC16_INTERNAL: [u64; PARTIAL_ROUNDS] = [
    0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0, 0x3c318939,
    0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d,
];

/// S-box: `x^7` over Baby Bear.
fn sbox(x: u64) -> u64 {
    let x2 = bb_mul(x, x);
    let x4 = bb_mul(x2, x2);
    bb_mul(x4, bb_mul(x2, x))
}

/// Apply the 4×4 MDS `M_4 = circ(2, 3, 1, 1)` in place. Matches upstream
/// `apply_mat4`.
fn apply_mat4(x: &mut [u64; 4]) {
    let t01 = bb_add(x[0], x[1]);
    let t23 = bb_add(x[2], x[3]);
    let t0123 = bb_add(t01, t23);
    let t01123 = bb_add(t0123, x[1]);
    let t01233 = bb_add(t0123, x[3]);
    let two_x0 = bb_add(x[0], x[0]);
    let two_x2 = bb_add(x[2], x[2]);
    let new3 = bb_add(t01233, two_x0);
    let new1 = bb_add(t01123, two_x2);
    let new0 = bb_add(t01123, t01);
    let new2 = bb_add(t01233, t23);
    x[0] = new0;
    x[1] = new1;
    x[2] = new2;
    x[3] = new3;
}

/// Apply the width-16 external MDS `M_E` in place. Matches upstream
/// `mds_light_permutation` with `WIDTH = 16`.
fn mds_light_permutation_16(state: &mut [u64; WIDTH]) {
    // Step 1: apply M_4 to each chunk of 4.
    let mut chunk: [u64; 4] = [0; 4];
    for kk in 0..(WIDTH / 4) {
        let k = kk * 4;
        chunk[0] = state[k];
        chunk[1] = state[k + 1];
        chunk[2] = state[k + 2];
        chunk[3] = state[k + 3];
        apply_mat4(&mut chunk);
        state[k] = chunk[0];
        state[k + 1] = chunk[1];
        state[k + 2] = chunk[2];
        state[k + 3] = chunk[3];
    }
    // Step 2: precompute sums[k] = Σ_{j ∈ {0, 4, 8, 12}} state[j + k].
    let mut sums: [u64; 4] = [0; 4];
    for kk in 0..4 {
        sums[kk] = bb_add(
            bb_add(state[kk], state[kk + 4]),
            bb_add(state[kk + 8], state[kk + 12]),
        );
    }
    // Step 3: state[i] += sums[i mod 4].
    for i in 0..WIDTH {
        state[i] = bb_add(state[i], sums[i % 4]);
    }
}

/// Apply the internal `1 + diag(V)` matrix in place, given the precomputed
/// sum of the state. Matches upstream `internal_layer_mat_mul` for width 16.
///
/// Diagonal V (over Baby Bear):
///   `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27,
///     -1/2^8, -1/16, -1/2^27]`
///
/// Result: `state'[i] = sum + V[i] · state[i]` (since `M_I = 1 + diag(V)`).
fn internal_mat_mul_16(state: &mut [u64; WIDTH], sum: u64) {
    // state[0]' = sum - 2·state[0]                       (V[0] = -2)
    let two_s0 = bb_add(state[0], state[0]);
    let new0 = bb_sub(sum, two_s0);

    // state[1]' = state[1] + sum                         (V[1] = 1)
    let new1 = bb_add(state[1], sum);
    // state[2]' = 2·state[2] + sum                       (V[2] = 2)
    let new2 = bb_add(bb_add(state[2], state[2]), sum);
    // state[3]' = state[3]/2 + sum                       (V[3] = 1/2)
    let new3 = bb_add(bb_div(state[3], 2), sum);
    // state[4]' = sum + 3·state[4]                       (V[4] = 3)
    let new4 = bb_add(sum, bb_mul(3, state[4]));
    // state[5]' = sum + 4·state[5]                       (V[5] = 4)
    let new5 = bb_add(sum, bb_mul(4, state[5]));
    // state[6]' = sum - state[6]/2                       (V[6] = -1/2)
    let new6 = bb_sub(sum, bb_div(state[6], 2));
    // state[7]' = sum - 3·state[7]                       (V[7] = -3)
    let new7 = bb_sub(sum, bb_mul(3, state[7]));
    // state[8]' = sum - 4·state[8]                       (V[8] = -4)
    let new8 = bb_sub(sum, bb_mul(4, state[8]));
    // state[9]' = state[9]/2^8 + sum                     (V[9] = 1/2^8)
    let new9 = bb_add(bb_div(state[9], 256), sum);
    // state[10]' = state[10]/4 + sum                     (V[10] = 1/4)
    let new10 = bb_add(bb_div(state[10], 4), sum);
    // state[11]' = state[11]/8 + sum                     (V[11] = 1/8)
    let new11 = bb_add(bb_div(state[11], 8), sum);
    // state[12]' = state[12]/2^27 + sum                  (V[12] = 1/2^27)
    let new12 = bb_add(bb_div(state[12], 1u64 << 27), sum);
    // state[13]' = sum - state[13]/2^8                   (V[13] = -1/2^8)
    let new13 = bb_sub(sum, bb_div(state[13], 256));
    // state[14]' = sum - state[14]/16                    (V[14] = -1/16)
    let new14 = bb_sub(sum, bb_div(state[14], 16));
    // state[15]' = sum - state[15]/2^27                  (V[15] = -1/2^27)
    let new15 = bb_sub(sum, bb_div(state[15], 1u64 << 27));

    state[0] = new0;
    state[1] = new1;
    state[2] = new2;
    state[3] = new3;
    state[4] = new4;
    state[5] = new5;
    state[6] = new6;
    state[7] = new7;
    state[8] = new8;
    state[9] = new9;
    state[10] = new10;
    state[11] = new11;
    state[12] = new12;
    state[13] = new13;
    state[14] = new14;
    state[15] = new15;
}

/// One full external round: add round constants, full-state S-box, MDS.
fn external_round_16(state: &mut [u64; WIDTH], rc: &[u64; WIDTH]) {
    for i in 0..WIDTH {
        state[i] = sbox(bb_add(state[i], rc[i]));
    }
    mds_light_permutation_16(state);
}

/// One partial round: add round constant to `state[0]`, S-box `state[0]`,
/// then internal MDS.
fn internal_round_16(state: &mut [u64; WIDTH], rc: u64) {
    state[0] = sbox(bb_add(state[0], rc));
    let mut sum: u64 = 0;
    for i in 0..WIDTH {
        sum = bb_add(sum, state[i]);
    }
    internal_mat_mul_16(state, sum);
}

/// Apply the Poseidon2 permutation in place to a width-16 Baby Bear state.
///
/// Every cell must be canonical (in `[0, p)`). The result, as canonical
/// representatives, is that of `default_babybear_poseidon2_16().permute_mut`
/// in `p3-baby-bear` 0.5.
pub fn poseidon2_permute_16(state: &mut [u64; WIDTH]) {
    // Linear pre-mix.
    mds_light_permutation_16(state);
    // 4 initial external rounds.
    for r in 0..HALF_FULL_ROUNDS {
        external_round_16(state, &RC16_EXTERNAL_INITIAL[r]);
    }
    // 13 partial rounds.
    for p in 0..PARTIAL_ROUNDS {
        internal_round_16(state, RC16_INTERNAL[p]);
    }
    // 4 terminal external rounds.
    for r in 0..HALF_FULL_ROUNDS {
        external_round_16(state, &RC16_EXTERNAL_FINAL[r]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sbox_x7() {
        assert_eq!(sbox(0), 0);
        assert_eq!(sbox(1), 1);
        assert_eq!(sbox(2), 128);
        // (p-1)^7 = p-1 in Baby Bear (since (p-1)^2 = 1, and 7 is odd).
        assert_eq!(sbox(BABY_BEAR_PRIME - 1), BABY_BEAR_PRIME - 1);
    }

    #[test]
    fn test_apply_mat4_zero() {
        let mut x = [0u64; 4];
        apply_mat4(&mut x);
        assert_eq!(x, [0, 0, 0, 0]);
    }

    #[test]
    fn test_apply_mat4_one_hot() {
        // M_4 first row = (2, 3, 1, 1). Apply to (1, 0, 0, 0) → (2, 1, 1, 3).
        let mut x = [1u64, 0, 0, 0];
        apply_mat4(&mut x);
        assert_eq!(x, [2, 1, 1, 3]);
    }

    #[test]
    fn test_apply_mat4_matches_matrix() {
        // M_4 with rows (2,3,1,1), (1,2,3,1), (1,1,2,3), (3,1,1,2), applied to
        // (a, b, c, d) with pairwise distinct entries.
        let m: [[u64; 4]; 4] = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
        let v: [u64; 4] = [5, BABY_BEAR_PRIME - 7, 11, 1 << 30];
        let mut x = v;
        apply_mat4(&mut x);
        for r in 0..4 {
            let mut expected = 0;
            for c in 0..4 {
                expected = bb_add(expected, bb_mul(m[r][c], v[c]));
            }
            assert_eq!(x[r], expected, "row {}", r);
        }
    }

    #[test]
    fn test_mds_light_perm_zero() {
        let mut s = [0u64; WIDTH];
        mds_light_permutation_16(&mut s);
        assert_eq!(s, [0u64; WIDTH]);
    }

    #[test]
    fn test_mds_light_perm_one_hot() {
        // M_E e_0 is column 0 of circ(2·M_4, M_4, M_4, M_4): 2·(2,1,1,3)
        // in the first block and (2,1,1,3) in the three others.
        let mut s = [0u64; WIDTH];
        s[0] = 1;
        mds_light_permutation_16(&mut s);
        assert_eq!(s, [4, 2, 2, 6, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3]);
    }

    #[test]
    fn test_internal_mat_mul_diagonal() {
        // For a one-hot state e_i the internal layer, called with sum = 1,
        // returns 1 + V[i] in cell i and 1 elsewhere.
        let v: [u64; WIDTH] = [
            bb_neg(2),
            1,
            2,
            bb_inv(2),
            3,
            4,
            bb_neg(bb_inv(2)),
            bb_neg(3),
            bb_neg(4),
            bb_inv(1 << 8),
            bb_inv(4),
            bb_inv(8),
            bb_inv(1 << 27),
            bb_neg(bb_inv(1 << 8)),
            bb_neg(bb_inv(16)),
            bb_neg(bb_inv(1 << 27)),
        ];
        for i in 0..WIDTH {
            let mut s = [0u64; WIDTH];
            s[i] = 1;
            internal_mat_mul_16(&mut s, 1);
            for j in 0..WIDTH {
                let expected = if i == j { bb_add(1, v[i]) } else { 1 };
                assert_eq!(s[j], expected, "row {} column {}", j, i);
            }
        }
    }
}
