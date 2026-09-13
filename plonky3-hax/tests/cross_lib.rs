//! Cross-check of `specs::baby_bear` against the field `BabyBear` of
//! `p3-baby-bear` 0.5, an independent implementation in Montgomery form.
//!
//! Inputs are canonical `u64` values; they are lifted with `BabyBear::new`
//! and results are compared through `as_canonical_u32`. Compared:
//!
//! 1. `bb_add`, `bb_sub`, `bb_neg`, `bb_mul`, `bb_square`, `bb_div` and
//!    `bb_inv` on every pair of the edge values `0, 1, 2, p - 2, p - 1`, on
//!    proptest inputs and on 1000 inputs from a fixed-seed generator;
//! 2. `bb_inv(0) = 0`, where Plonky3's `try_inverse` returns `None`;
//! 3. `bb_pow` against `exp_u64` for exponents below 256, for edge
//!    exponents up to `u64::MAX`, and for random 64-bit exponents;
//! 4. `bb_root_of_unity(k)` against `two_adic_generator(k)`, `k = 0..=27`;
//! 5. `bb_poly_eval` against Horner evaluation in `BabyBear`.

use p3_baby_bear::BabyBear;
use p3_field::integers::QuotientMap;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField};
use plonky3_hax::specs::baby_bear::*;
use proptest::prelude::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// Lift a canonical `u64` in `[0, p)` into the upstream field type.
fn lift(v: u64) -> BabyBear {
    // `BabyBear::new` takes a u32 and reduces modulo p.
    BabyBear::new(v as u32)
}

/// Read the canonical `u64` representative out of an upstream field element.
fn project(x: BabyBear) -> u64 {
    x.as_canonical_u32() as u64
}

fn bb_element() -> impl Strategy<Value = u64> {
    (0u64..BABY_BEAR_PRIME).boxed()
}

// ========================================================================
// Proptest-driven equivalence on random inputs
// ========================================================================

proptest! {
    #[test]
    fn cross_add(a in bb_element(), b in bb_element()) {
        let ours = bb_add(a, b);
        let theirs = project(lift(a) + lift(b));
        prop_assert_eq!(ours, theirs);
    }

    #[test]
    fn cross_sub(a in bb_element(), b in bb_element()) {
        let ours = bb_sub(a, b);
        let theirs = project(lift(a) - lift(b));
        prop_assert_eq!(ours, theirs);
    }

    #[test]
    fn cross_neg(a in bb_element()) {
        let ours = bb_neg(a);
        let theirs = project(-lift(a));
        prop_assert_eq!(ours, theirs);
    }

    #[test]
    fn cross_mul(a in bb_element(), b in bb_element()) {
        let ours = bb_mul(a, b);
        let theirs = project(lift(a) * lift(b));
        prop_assert_eq!(ours, theirs);
    }

    #[test]
    fn cross_inv_nonzero(a in 1u64..BABY_BEAR_PRIME) {
        let ours = bb_inv(a);
        let theirs = project(lift(a).try_inverse().expect("nonzero has inverse"));
        prop_assert_eq!(ours, theirs);
    }

    #[test]
    fn cross_mul_identity_holds_both_sides(
        a in 1u64..BABY_BEAR_PRIME,
    ) {
        // a * inv(a) == 1 in both implementations.
        prop_assert_eq!(bb_mul(a, bb_inv(a)), 1);
        let up = lift(a) * lift(a).try_inverse().unwrap();
        prop_assert_eq!(project(up), 1);
    }

    #[test]
    fn cross_pow_small_exp(base in bb_element(), exp in 0u64..256) {
        let ours = bb_pow(base, exp);
        let mut theirs = BabyBear::from_int(1u32);
        let b = lift(base);
        for _ in 0..exp {
            theirs *= b;
        }
        prop_assert_eq!(ours, project(theirs));
    }
}

// ========================================================================
// Fixed-seed inputs
// ========================================================================

#[test]
fn cross_determinism_fixed_seed() {
    // 1000 input pairs from a fixed-seed generator, independent of
    // proptest's sampler.
    let mut rng = StdRng::seed_from_u64(0xABCDEF0123456789);
    for _ in 0..1000 {
        let a: u64 = rng.gen_range(0..BABY_BEAR_PRIME);
        let b: u64 = rng.gen_range(0..BABY_BEAR_PRIME);
        assert_eq!(bb_add(a, b), project(lift(a) + lift(b)));
        assert_eq!(bb_sub(a, b), project(lift(a) - lift(b)));
        assert_eq!(bb_mul(a, b), project(lift(a) * lift(b)));
        assert_eq!(bb_neg(a), project(-lift(a)));
        if a != 0 {
            assert_eq!(bb_inv(a), project(lift(a).try_inverse().unwrap()));
        }
    }
}

// ========================================================================
// Polynomial evaluation cross-check
// ========================================================================

proptest! {
    #[test]
    fn cross_poly_eval(
        coeffs in prop::collection::vec(bb_element(), 1..=8),
        x in bb_element(),
    ) {
        let ours = bb_poly_eval(&coeffs, x);
        // Horner in upstream.
        let mut theirs = BabyBear::from_int(0u32);
        let xp = lift(x);
        for &c in coeffs.iter().rev() {
            theirs = theirs * xp + lift(c);
        }
        prop_assert_eq!(ours, project(theirs));
    }
}

// ========================================================================
// Edge values
// ========================================================================

const EDGE: [u64; 5] = [0, 1, 2, BABY_BEAR_PRIME - 2, BABY_BEAR_PRIME - 1];

#[test]
fn cross_edge_values_all_pairs() {
    for &a in EDGE.iter() {
        assert_eq!(bb_neg(a), project(-lift(a)), "neg {}", a);
        assert_eq!(bb_square(a), project(lift(a) * lift(a)), "square {}", a);
        assert_eq!(bb_reduce(a), a, "reduce {}", a);
        match lift(a).try_inverse() {
            Some(inv) => assert_eq!(bb_inv(a), project(inv), "inv {}", a),
            None => {
                assert_eq!(a, 0);
                assert_eq!(bb_inv(a), 0);
            }
        }
        for &b in EDGE.iter() {
            assert_eq!(bb_add(a, b), project(lift(a) + lift(b)), "add {} {}", a, b);
            assert_eq!(bb_sub(a, b), project(lift(a) - lift(b)), "sub {} {}", a, b);
            assert_eq!(bb_mul(a, b), project(lift(a) * lift(b)), "mul {} {}", a, b);
            if b != 0 {
                assert_eq!(bb_div(a, b), project(lift(a) / lift(b)), "div {} {}", a, b);
            } else {
                assert_eq!(bb_div(a, b), 0, "div {} 0", a);
            }
        }
    }
}

#[test]
fn cross_reduce_below_two_p() {
    for &x in &[BABY_BEAR_PRIME, BABY_BEAR_PRIME + 1, 2 * BABY_BEAR_PRIME - 1] {
        assert_eq!(bb_reduce(x), x - BABY_BEAR_PRIME);
    }
}

#[test]
fn cross_pow_edge_exponents() {
    let p = BABY_BEAR_PRIME;
    let exps: [u64; 12] = [
        0,
        1,
        2,
        7,
        p - 2,
        p - 1,
        p,
        p + 1,
        1u64 << 32,
        1u64 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    for &base in EDGE.iter().chain([3u64, 31, 0x5ee99486].iter()) {
        for &e in exps.iter() {
            assert_eq!(
                bb_pow(base, e),
                project(lift(base).exp_u64(e)),
                "pow {} {}",
                base,
                e
            );
        }
    }
}

#[test]
fn cross_pow_random_64_bit_exponents() {
    let mut rng = StdRng::seed_from_u64(0x0123456789ABCDEF);
    for _ in 0..200 {
        let base: u64 = rng.gen_range(0..BABY_BEAR_PRIME);
        let e: u64 = rng.gen();
        assert_eq!(bb_pow(base, e), project(lift(base).exp_u64(e)), "pow {} {}", base, e);
    }
}

#[test]
fn cross_two_adic_generators() {
    for k in 0..=27u32 {
        assert_eq!(
            bb_root_of_unity(k),
            project(BabyBear::two_adic_generator(k as usize)),
            "k = {}",
            k
        );
    }
}

#[test]
fn cross_poly_eval_edge_points() {
    assert_eq!(bb_poly_eval(&[], 5), 0);
    let mut rng = StdRng::seed_from_u64(7);
    let mut coeffs: Vec<u64> = Vec::new();
    for _ in 0..64 {
        coeffs.push(rng.gen_range(0..BABY_BEAR_PRIME));
    }
    for len in [1usize, 2, 17, 64] {
        for &x in EDGE.iter() {
            let mut theirs = BabyBear::ZERO;
            for &c in coeffs[..len].iter().rev() {
                theirs = theirs * lift(x) + lift(c);
            }
            assert_eq!(bb_poly_eval(&coeffs[..len], x), project(theirs), "len {} x {}", len, x);
        }
    }
}

// The upstream traits the tests use: `Field` (`try_inverse`, division),
// `PrimeField32` (`as_canonical_u32`), `QuotientMap` (`from_int`),
// `TwoAdicField` (`two_adic_generator`).
const _: fn() = || {
    let _y: BabyBear = <BabyBear as PrimeCharacteristicRing>::ONE;
    fn _f<F: Field + PrimeField + PrimeField32 + TwoAdicField>() {}
    _f::<BabyBear>();
};
