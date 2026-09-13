//! Arithmetic in the Baby Bear prime field F_p, p = 2^31 - 2^27 + 1.
//!
//! p = 0x78000001 = 2013265921, and p - 1 = 2^27 * 3 * 5, so F_p^* contains
//! a subgroup of order 2^k for every k <= 27. These are the parameters of
//! `BabyBearParameters` in Plonky3's `p3-baby-bear` 0.5 (`PRIME = 0x78000001`,
//! `MONTY_GEN = 31`, `TWO_ADICITY = 27`).
//!
//! Representation: an element is its canonical representative, a `u64` in
//! `[0, p)`. Plonky3 stores the Montgomery form `a * 2^32 mod p` in a `u32`;
//! the two representations denote the same field element, and the tests
//! compare canonical representatives (`as_canonical_u32`). Every function
//! below maps canonical inputs to a canonical output. Inputs outside `[0, p)`
//! are outside the specification: the output need not be canonical (for
//! example `bb_sub(p, 0) = p`).
//!
//! Multiplicative inversion is total: `bb_inv(0) = 0`, whereas Plonky3's
//! `try_inverse` returns `None` on zero.

/// The Baby Bear prime: p = 2^31 - 2^27 + 1.
pub const BABY_BEAR_PRIME: u64 = 2013265921;

/// Additive identity.
pub const ZERO: u64 = 0;

/// Multiplicative identity.
pub const ONE: u64 = 1;

/// A generator of the multiplicative group F_p^* (`MONTY_GEN` in `p3-baby-bear`).
///
/// The 2^k-th roots of unity are `bb_pow(GENERATOR, (p-1) / 2^k)`.
pub const GENERATOR: u64 = 31;

/// Reduce `x` to `[0, p)` by one conditional subtraction.
///
/// Requires `x < 2p`.
pub fn bb_reduce(x: u64) -> u64 {
    if x >= BABY_BEAR_PRIME {
        x - BABY_BEAR_PRIME
    } else {
        x
    }
}

/// Add two Baby Bear field elements: (a + b) mod p.
///
/// For canonical `a` and `b` the sum is below `2p`, so one conditional
/// subtraction reduces it.
pub fn bb_add(a: u64, b: u64) -> u64 {
    bb_reduce(a + b)
}

/// Subtract two Baby Bear field elements: (a - b) mod p.
///
/// If `a < b`, the result is `a + p - b`.
pub fn bb_sub(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        a + BABY_BEAR_PRIME - b
    }
}

/// Negate a Baby Bear field element: `(-a) mod p`, which is `p - a` for
/// `a != 0` and `0` for `a = 0`.
pub fn bb_neg(a: u64) -> u64 {
    if a == 0 {
        0
    } else {
        BABY_BEAR_PRIME - a
    }
}

/// Multiply two Baby Bear field elements: (a * b) mod p.
///
/// The product is formed in `u128` and reduced with `%`. For canonical
/// inputs it is below 2^62, so the widening only removes the overflow case
/// for non-canonical inputs.
pub fn bb_mul(a: u64, b: u64) -> u64 {
    let product: u128 = (a as u128) * (b as u128);
    (product % (BABY_BEAR_PRIME as u128)) as u64
}

/// Square a Baby Bear field element: a^2 mod p.
pub fn bb_square(a: u64) -> u64 {
    bb_mul(a, a)
}

/// Compute `base^exp mod p` by right-to-left square-and-multiply.
///
/// `exp` is any `u64`; the loop runs at most 64 iterations, one per exponent
/// bit, and `bb_pow(base, 0) = 1` for every `base`, including `0`.
pub fn bb_pow(base: u64, exp: u64) -> u64 {
    if exp == 0 {
        return ONE;
    }

    let mut result: u64 = ONE;
    let mut cur_base: u64 = base;
    let mut e: u64 = exp;

    for _ in 0..64 {
        if e & 1 == 1 {
            result = bb_mul(result, cur_base);
        }
        cur_base = bb_square(cur_base);
        e >>= 1;
        if e == 0 {
            break;
        }
    }

    result
}

/// Compute the multiplicative inverse of a: a^{-1} mod p.
///
/// Computed as `a^(p-2)` (Fermat's little theorem). Returns `0` for `a = 0`.
pub fn bb_inv(a: u64) -> u64 {
    if a == 0 {
        return ZERO;
    }
    bb_pow(a, BABY_BEAR_PRIME - 2)
}

/// Division: `a * bb_inv(b)`, hence `bb_div(a, 0) = 0`.
pub fn bb_div(a: u64, b: u64) -> u64 {
    bb_mul(a, bb_inv(b))
}

/// Compute a primitive 2^k-th root of unity in the Baby Bear field.
///
/// Returns `GENERATOR^((p-1) / 2^k)`, which has multiplicative order exactly
/// `2^k`. Requires `k <= 27`; the values for `k = 0..=27` equal
/// `TWO_ADIC_GENERATORS[k]` of `p3-baby-bear` 0.5.
pub fn bb_root_of_unity(k: u32) -> u64 {
    let p_minus_one: u64 = BABY_BEAR_PRIME - 1;
    let exponent: u64 = p_minus_one >> k;
    bb_pow(GENERATOR, exponent)
}

/// Evaluate a polynomial at a point using Horner's method.
///
/// `coeffs[i]` is the coefficient of `x^i`; the empty polynomial evaluates
/// to `0`.
pub fn bb_poly_eval(coeffs: &[u64], point: u64) -> u64 {
    let len = coeffs.len();
    if len == 0 {
        return ZERO;
    }

    let mut result: u64 = coeffs[len - 1];
    for i in 1..len {
        result = bb_add(bb_mul(result, point), coeffs[len - 1 - i]);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_baby_bear_prime_value() {
        // p = 2^31 - 2^27 + 1
        let computed: u64 = (1u64 << 31) - (1u64 << 27) + 1;
        assert_eq!(BABY_BEAR_PRIME, computed);
        assert_eq!(BABY_BEAR_PRIME, 2013265921);
    }

    #[test]
    fn test_bb_add_basic() {
        assert_eq!(bb_add(0, 0), 0);
        assert_eq!(bb_add(1, 0), 1);
        assert_eq!(bb_add(1, 1), 2);
        // Wraparound
        let p_minus_1 = BABY_BEAR_PRIME - 1;
        assert_eq!(bb_add(p_minus_1, 1), 0);
        assert_eq!(bb_add(p_minus_1, 2), 1);
    }

    #[test]
    fn test_bb_sub_basic() {
        assert_eq!(bb_sub(5, 3), 2);
        assert_eq!(bb_sub(0, 0), 0);
        assert_eq!(bb_sub(0, 1), BABY_BEAR_PRIME - 1);
    }

    #[test]
    fn test_bb_neg() {
        assert_eq!(bb_neg(0), 0);
        assert_eq!(bb_add(42, bb_neg(42)), 0);
        assert_eq!(bb_neg(1), BABY_BEAR_PRIME - 1);
    }

    #[test]
    fn test_bb_mul_basic() {
        assert_eq!(bb_mul(0, 42), 0);
        assert_eq!(bb_mul(1, 42), 42);
        assert_eq!(bb_mul(2, 3), 6);
        // (p-1)^2 = 1 mod p
        let p_minus_1 = BABY_BEAR_PRIME - 1;
        assert_eq!(bb_mul(p_minus_1, p_minus_1), 1);
    }

    #[test]
    fn test_bb_mul_distributive() {
        let a: u64 = 12345;
        let b: u64 = 67890;
        let c: u64 = 111111;
        // a * (b + c) = a*b + a*c
        let lhs = bb_mul(a, bb_add(b, c));
        let rhs = bb_add(bb_mul(a, b), bb_mul(a, c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_bb_pow() {
        assert_eq!(bb_pow(7, 0), 1);
        assert_eq!(bb_pow(7, 1), 7);
        assert_eq!(bb_pow(2, 10), 1024);
        // Fermat's little theorem: a^(p-1) = 1
        assert_eq!(bb_pow(31, BABY_BEAR_PRIME - 1), 1);
        assert_eq!(bb_pow(7, BABY_BEAR_PRIME - 1), 1);
    }

    #[test]
    fn test_bb_inv() {
        assert_eq!(bb_inv(0), 0);
        let a: u64 = 42;
        assert_eq!(bb_mul(a, bb_inv(a)), 1);
        let b: u64 = 1234567;
        assert_eq!(bb_mul(b, bb_inv(b)), 1);
    }

    #[test]
    fn test_bb_root_of_unity() {
        // A 2^k-th root of unity satisfies omega^(2^k) = 1
        let k: u32 = 8;
        let omega = bb_root_of_unity(k);
        let order: u64 = 1u64 << k;
        assert_eq!(bb_pow(omega, order), 1);
        // omega^(2^(k-1)) should be -1 (= p-1) for a primitive 2^k-th root
        assert_eq!(bb_pow(omega, order >> 1), BABY_BEAR_PRIME - 1);
    }

    #[test]
    fn test_bb_root_of_unity_max() {
        // k = 27 is the maximum: p - 1 = 2^27 * 15
        let k: u32 = 27;
        let omega = bb_root_of_unity(k);
        let order: u64 = 1u64 << k;
        assert_eq!(bb_pow(omega, order), 1);
        assert_eq!(bb_pow(omega, order >> 1), BABY_BEAR_PRIME - 1);
    }

    #[test]
    fn test_bb_poly_eval() {
        // p(x) = 3x^2 + 2x + 1
        let coeffs = [1u64, 2, 3];
        assert_eq!(bb_poly_eval(&coeffs, 0), 1);
        assert_eq!(bb_poly_eval(&coeffs, 1), 6);
        assert_eq!(bb_poly_eval(&coeffs, 2), 17);
        assert_eq!(bb_poly_eval(&coeffs, 10), 321);
    }

    #[test]
    fn test_bb_poly_eval_constant() {
        let coeffs = [42u64];
        assert_eq!(bb_poly_eval(&coeffs, 0), 42);
        assert_eq!(bb_poly_eval(&coeffs, 999), 42);
    }
}
