//! Cross-check of `specs::poseidon2::poseidon2_permute_16` against
//! `default_babybear_poseidon2_16()` of `p3-baby-bear` 0.5 (built on
//! `p3-poseidon2` 0.5), an independent implementation over the
//! Montgomery-form field.
//!
//! 1. The round constants equal `BABYBEAR_POSEIDON2_RC_16_*`.
//! 2. The permutations agree on the zero state, the all-`(p - 1)` state, a
//!    one-hot state, the state `(0, 1, …, 15)`, the one-hot states at every
//!    position with value `p - 1`, 20 states from a fixed-seed generator,
//!    and proptest states.

use p3_baby_bear::{
    default_babybear_poseidon2_16, Poseidon2BabyBear, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL, BABYBEAR_POSEIDON2_RC_16_INTERNAL,
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_symmetric::Permutation;
use plonky3_hax::specs::baby_bear::*;
use plonky3_hax::specs::poseidon2::*;
use proptest::prelude::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

fn lift_state(s: &[u64; 16]) -> [p3_baby_bear::BabyBear; 16] {
    let mut out = [p3_baby_bear::BabyBear::ZERO; 16];
    for (i, &v) in s.iter().enumerate() {
        out[i] = p3_baby_bear::BabyBear::new(v as u32);
    }
    out
}

fn project_state(s: &[p3_baby_bear::BabyBear; 16]) -> [u64; 16] {
    let mut out = [0u64; 16];
    for (i, v) in s.iter().enumerate() {
        out[i] = v.as_canonical_u32() as u64;
    }
    out
}

fn upstream_permute(input: &[u64; 16]) -> [u64; 16] {
    let perm: Poseidon2BabyBear<16> = default_babybear_poseidon2_16();
    let mut s = lift_state(input);
    perm.permute_mut(&mut s);
    project_state(&s)
}

#[test]
fn poseidon2_round_constants_match_upstream() {
    for r in 0..HALF_FULL_ROUNDS {
        assert_eq!(
            RC16_EXTERNAL_INITIAL[r],
            project_state(&BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL[r]),
            "initial round {}",
            r
        );
        assert_eq!(
            RC16_EXTERNAL_FINAL[r],
            project_state(&BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL[r]),
            "final round {}",
            r
        );
    }
    for p in 0..PARTIAL_ROUNDS {
        assert_eq!(
            RC16_INTERNAL[p],
            BABYBEAR_POSEIDON2_RC_16_INTERNAL[p].as_canonical_u32() as u64,
            "partial round {}",
            p
        );
    }
}

#[test]
fn poseidon2_equiv_max_state() {
    let input = [BABY_BEAR_PRIME - 1; 16];
    let mut ours = input;
    poseidon2_permute_16(&mut ours);
    assert_eq!(ours, upstream_permute(&input));
}

#[test]
fn poseidon2_equiv_one_hot_max_every_position() {
    for i in 0..16 {
        let mut input = [0u64; 16];
        input[i] = BABY_BEAR_PRIME - 1;
        let mut ours = input;
        poseidon2_permute_16(&mut ours);
        assert_eq!(ours, upstream_permute(&input), "position {}", i);
    }
}

#[test]
fn poseidon2_equiv_zero_state() {
    let input = [0u64; 16];
    let mut ours = input;
    poseidon2_permute_16(&mut ours);
    let theirs = upstream_permute(&input);
    assert_eq!(
        ours, theirs,
        "Poseidon2 disagreement on the zero state\n  ours:   {:?}\n  theirs: {:?}",
        ours, theirs
    );
}

#[test]
fn poseidon2_equiv_one_hot_state() {
    let mut input = [0u64; 16];
    input[0] = 1;
    let mut ours = input;
    poseidon2_permute_16(&mut ours);
    let theirs = upstream_permute(&input);
    assert_eq!(ours, theirs);
}

#[test]
fn poseidon2_equiv_counting_state() {
    let input: [u64; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let mut ours = input;
    poseidon2_permute_16(&mut ours);
    let theirs = upstream_permute(&input);
    assert_eq!(ours, theirs);
}

#[test]
fn poseidon2_equiv_random_states_seed42() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let mut input = [0u64; 16];
        for v in input.iter_mut() {
            *v = rng.gen_range(0..BABY_BEAR_PRIME);
        }
        let mut ours = input;
        poseidon2_permute_16(&mut ours);
        let theirs = upstream_permute(&input);
        assert_eq!(ours, theirs, "seed=42 input={:?}", input);
    }
}

proptest! {
    #[test]
    fn prop_poseidon2_matches_upstream(values in proptest::collection::vec(0u64..BABY_BEAR_PRIME, 16)) {
        let mut input = [0u64; 16];
        for (i, &v) in values.iter().enumerate() {
            input[i] = v;
        }
        let mut ours = input;
        poseidon2_permute_16(&mut ours);
        let theirs = upstream_permute(&input);
        prop_assert_eq!(ours, theirs);
    }
}
