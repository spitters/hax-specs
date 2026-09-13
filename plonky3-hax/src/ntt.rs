//! Radix-2 Number-Theoretic Transform over the Baby Bear field.
//!
//! Iterative Cooley–Tukey, in-place, no recursion, no closures — written
//! to be straightforwardly hax-extractable. Both the forward NTT (DFT)
//! and the inverse NTT (iDFT) operate on slices whose length is a power
//! of two; the caller is responsible for that.
//!
//! ## Usage
//!
//! Given evaluations of a polynomial `P(x)` at the multiplicative subgroup
//! `H = {ω^0, ω^1, ..., ω^(n-1)}` of size `n = 2^k`, where `ω` is a
//! primitive `n`-th root of unity:
//!
//! - `intt(evals, ω)` rewrites `evals` in place into the coefficients of
//!   `P(x)`, i.e. `evals[i]` becomes the coefficient of `x^i`.
//!
//! - `ntt(coeffs, ω)` is the inverse: given coefficients in standard
//!   monomial order, rewrites them in place into evaluations on `H`.
//!
//! Calling `ntt(.., ω)` then `intt(.., ω)` (or vice versa) on the same
//! slice with the same `ω` is the identity.

use crate::specs::baby_bear::*;

/// Reverse the low `log_n` bits of `i`.
fn bit_reverse(i: u64, log_n: u32) -> u64 {
    let mut x = i;
    let mut r: u64 = 0;
    for _ in 0..log_n {
        r = (r << 1) | (x & 1);
        x >>= 1;
    }
    r
}

/// Forward NTT: evaluations of a polynomial at `{ω^0, ..., ω^(n-1)}` from
/// its coefficient sequence in monomial order. In place.
///
/// `omega` must be a primitive `n`-th root of unity in Baby Bear, where
/// `n = vals.len()` is a power of two.
pub fn ntt(vals: &mut [u64], omega: u64) {
    let n = vals.len();
    // Avoid an early `return` in the small case: an early return mixes
    // a `()` tail with the array-typed loop tail in the Lean translation's
    // mutation lifting. Wrap the whole non-trivial body inside one
    // `if n > 1`.
    if n > 1 {
    // n is assumed to be a power of two; trailing_zeros gives log_2(n).
    let log_n: u32 = n.trailing_zeros();

    // 1. Bit-reverse permutation.
    for i in 0..n {
        let j = bit_reverse(i as u64, log_n) as usize;
        if i < j {
            vals.swap(i, j);
        }
    }

    // 2. Iterative Cooley–Tukey butterflies. Layer `layer` uses
    //    `size = 1 << (layer + 1)`; the outer loop runs `log_n` times.
    //    Computing `size` from the iteration index instead of carrying
    //    it as mutable state keeps the body's accumulator a single
    //    value (`vals`); the Lean translation's `foldRange` lifting drops the
    //    extra state otherwise.
    for layer in 0..log_n {
        let size: usize = 1usize << (layer + 1);
        let half = size / 2;
        // ω_size = ω^(n / size) is a primitive `size`-th root of unity.
        let w_size = bb_pow(omega, (n / size) as u64);

        let n_blocks = n / size;
        for b in 0..n_blocks {
            let block = b * size;
            // Compute w_pow = w_size^j inside the loop rather than
            // carrying it as mutable state. Keeps the body's
            // accumulator a single `vals` slice; the Lean translation's
            // `foldRange` cannot lift multi-state tuples cleanly.
            for j in 0..half {
                let w_pow = bb_pow(w_size, j as u64);
                let t = bb_mul(w_pow, vals[block + j + half]);
                vals[block + j + half] = bb_sub(vals[block + j], t);
                vals[block + j] = bb_add(vals[block + j], t);
            }
        }
    }
    }
}

/// Inverse NTT: coefficient sequence from evaluations at `{ω^0, ..., ω^(n-1)}`.
/// In place. `omega` is the same primitive root used in [`ntt`].
pub fn intt(vals: &mut [u64], omega: u64) {
    let n = vals.len();
    if n > 1 {
        // Inverse NTT = forward NTT with ω^{-1}, scaled by 1/n.
        let omega_inv = bb_inv(omega);
        ntt(vals, omega_inv);

        let n_inv = bb_inv(n as u64);
        for i in 0..n {
            vals[i] = bb_mul(vals[i], n_inv);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_reverse_small() {
        // log_n = 3 reverses 3-bit indices.
        assert_eq!(bit_reverse(0b000, 3), 0b000);
        assert_eq!(bit_reverse(0b001, 3), 0b100);
        assert_eq!(bit_reverse(0b011, 3), 0b110);
        assert_eq!(bit_reverse(0b111, 3), 0b111);
    }

    #[test]
    fn test_ntt_intt_round_trip() {
        // Round-trip on a fixed coefficient vector at n = 8.
        let omega = bb_root_of_unity(3); // primitive 8th root
        let original: Vec<u64> = vec![7, 11, 13, 17, 19, 23, 29, 31];

        let mut v = original.clone();
        ntt(&mut v, omega);
        intt(&mut v, omega);
        assert_eq!(v, original);

        let mut v2 = original.clone();
        intt(&mut v2, omega);
        ntt(&mut v2, omega);
        assert_eq!(v2, original);
    }

    #[test]
    fn test_ntt_constant_polynomial() {
        // P(x) = c maps to (c, c, c, ..., c) under any NTT.
        let omega = bb_root_of_unity(2); // n = 4
        let mut v = vec![42u64, 0, 0, 0];
        ntt(&mut v, omega);
        assert_eq!(v, vec![42u64, 42, 42, 42]);
    }

    #[test]
    fn test_ntt_dirac_at_zero() {
        // Coefficient vector (1, 0, 0, ...) corresponds to the constant
        // polynomial P(x) = 1. NTT result: all-ones.
        let omega = bb_root_of_unity(3);
        let mut v = vec![1u64, 0, 0, 0, 0, 0, 0, 0];
        ntt(&mut v, omega);
        assert_eq!(v, vec![1u64; 8]);
    }

    #[test]
    fn test_ntt_matches_naive_eval() {
        // Compare NTT against direct polynomial evaluation at ω^i for
        // every i, on a small coefficient vector.
        let log_n: u32 = 3;
        let n = 1usize << log_n;
        let omega = bb_root_of_unity(log_n);
        let coeffs: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, 8];

        let mut via_ntt = coeffs.clone();
        ntt(&mut via_ntt, omega);

        let mut expected: Vec<u64> = Vec::with_capacity(n);
        for i in 0..n {
            let x = bb_pow(omega, i as u64);
            expected.push(bb_poly_eval(&coeffs, x));
        }
        assert_eq!(via_ntt, expected);
    }
}
