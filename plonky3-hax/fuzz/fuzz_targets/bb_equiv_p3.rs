#![no_main]
//! Differential fuzz target: `specs::baby_bear` against the Montgomery-form
//! field of Plonky3's `p3-baby-bear` 0.5.
//!
//! For each input the target reduces two `u32` values modulo p, runs every
//! field operation in both implementations, and asserts that the canonical
//! representatives agree.
//!
//! Run: `cargo +nightly fuzz run bb_equiv_p3 -- -max_total_time=300`

use libfuzzer_sys::fuzz_target;

use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use plonky3_hax::specs::baby_bear::*;

fn lift(v: u64) -> BabyBear {
    BabyBear::new(v as u32)
}

fn project(x: BabyBear) -> u64 {
    x.as_canonical_u32() as u64
}

#[derive(arbitrary::Arbitrary, Debug)]
struct Input {
    a_raw: u32,
    b_raw: u32,
    exp: u8,
}

fuzz_target!(|input: Input| {
    let a = (input.a_raw as u64) % BABY_BEAR_PRIME;
    let b = (input.b_raw as u64) % BABY_BEAR_PRIME;

    assert_eq!(bb_add(a, b), project(lift(a) + lift(b)));
    assert_eq!(bb_sub(a, b), project(lift(a) - lift(b)));
    assert_eq!(bb_neg(a), project(-lift(a)));
    assert_eq!(bb_mul(a, b), project(lift(a) * lift(b)));
    assert_eq!(bb_square(a), project(lift(a) * lift(a)));

    let e = input.exp as u64;
    assert_eq!(bb_pow(a, e), project(lift(a).exp_u64(e)));

    if a != 0 {
        assert_eq!(
            bb_inv(a),
            project(lift(a).try_inverse().expect("nonzero has inverse"))
        );
        assert_eq!(bb_div(a, a), 1);
    }
});
