# plonky3-hax

The Baby Bear prime field and the width-16 Poseidon2 permutation, as
instantiated by [Plonky3](https://github.com/Plonky3/Plonky3) 0.5, written in
the fragment of Rust that [hax](https://github.com/cryspen/hax) extracts to
Lean. The crate also contains a reference STARK over the same field (AIR,
FRI-style folding, quotient, DEEP and proof-of-work steps), which follows no
published specification; see [Reference STARK](#reference-stark). The code is
a reference specification: it is not constant-time and is not tuned for
speed.

## Specifications

- **Baby Bear field** (`src/specs/baby_bear.rs`): F_p with
  p = 2^31 − 2^27 + 1 = `0x78000001`, the field `BabyBear` of `p3-baby-bear`
  0.5 (`BabyBearParameters`: `PRIME = 0x78000001`, `MONTY_GEN = 31`,
  `TWO_ADICITY = 27`). Elements are canonical representatives in `[0, p)`
  stored in `u64`; Plonky3 stores the Montgomery form `a · 2^32 mod p` in
  `u32`. Both denote the same field element, and all comparisons are made on
  canonical representatives. `bb_inv(0)` and `bb_div(a, 0)` return `0`,
  where Plonky3's `try_inverse` returns `None`. `bb_root_of_unity(k)` is
  `31^((p−1)/2^k)` for `k ≤ 27`, equal to Plonky3's
  `two_adic_generator(k)`.
- **Poseidon2, width 16** (`src/specs/poseidon2.rs`): the permutation of
  `default_babybear_poseidon2_16()` in `p3-baby-bear` 0.5, with the round
  structure of Grassi, Khovratovich and Schofnegger, *Poseidon2: A Faster
  Version of the Poseidon Hash Function* (IACR ePrint 2023/323).

Poseidon2 parameters:

| Parameter | Value | Plonky3 0.5 source |
|---|---|---|
| Width `t` | 16 | `Poseidon2BabyBear<16>` |
| S-box | `x^7` | `BABYBEAR_S_BOX_DEGREE = 7` |
| Full rounds `R_F` | 8 (4 before, 4 after the partial rounds) | `BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS = 4` |
| Partial rounds `R_P` | 13 | `BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16 = 13` |
| 4×4 matrix | `circ(2, 3, 1, 1)` | `MDSMat4` (`p3-poseidon2`) |
| External matrix | `circ(2·M_4, M_4, M_4, M_4)`, also applied once before the first round | `mds_light_permutation` (`p3-poseidon2`) |
| Internal matrix | `1 + diag(V)`, `V = [−2, 1, 2, 1/2, 3, 4, −1/2, −3, −4, 1/2^8, 1/4, 1/8, 1/2^27, −1/2^8, −1/16, −1/2^27]` | `BabyBearInternalLayerParameters` |
| Round constants | `RC16_EXTERNAL_INITIAL`, `RC16_INTERNAL`, `RC16_EXTERNAL_FINAL` | `BABYBEAR_POSEIDON2_RC_16_{EXTERNAL_INITIAL, INTERNAL, EXTERNAL_FINAL}` |

The HorizenLabs reference implementation of Poseidon2
(`poseidon2_instance_babybear.rs`) defines a width-16 Baby Bear instance
with another 4×4 matrix and another internal diagonal; it is a different
permutation from the one specified here.

## Public API

```rust
// specs::baby_bear
pub const BABY_BEAR_PRIME: u64;             // 0x78000001
pub const GENERATOR: u64;                   // 31
pub fn bb_reduce(x: u64) -> u64;            // requires x < 2p
pub fn bb_add(a: u64, b: u64) -> u64;
pub fn bb_sub(a: u64, b: u64) -> u64;
pub fn bb_neg(a: u64) -> u64;
pub fn bb_mul(a: u64, b: u64) -> u64;
pub fn bb_square(a: u64) -> u64;
pub fn bb_pow(base: u64, exp: u64) -> u64;
pub fn bb_inv(a: u64) -> u64;               // bb_inv(0) = 0
pub fn bb_div(a: u64, b: u64) -> u64;       // bb_div(a, 0) = 0
pub fn bb_root_of_unity(k: u32) -> u64;     // requires k <= 27
pub fn bb_poly_eval(coeffs: &[u64], point: u64) -> u64;

// specs::poseidon2
pub fn poseidon2_permute_16(state: &mut [u64; 16]);
```

All field functions take and return canonical representatives.

## Test vectors and their provenance

| File | Source | Coverage |
|---|---|---|
| `tests/plonky3_vectors.rs` | `p3-baby-bear` 0.5.2 sources: `src/poseidon2.rs`, test `test_default_babybear_poseidon2_width_16`; `src/baby_bear.rs`, `TwoAdicData` and `RelativelyPrimePower<7>` constants | one Poseidon2 input/output pair; `TWO_ADIC_GENERATORS[0..=27]`, `ROOTS_8`, `INV_ROOTS_8`, `ROOTS_16`, `INV_ROOTS_16`; `PRIME`, `MONTY_GEN`; the 7-th root exponent `1725656503` |
| `tests/poseidon2_cross.rs` | `p3-baby-bear` 0.5 as oracle | round constants; zero, all-`(p−1)`, one-hot and counting states; 20 fixed-seed and 256 proptest states |
| `tests/cross_lib.rs` | `p3-baby-bear` 0.5 and `p3-field` 0.5 as oracle | every field operation on all pairs of `0, 1, 2, p−2, p−1`, on 1000 fixed-seed and proptest inputs; `bb_pow` for exponents up to `u64::MAX`; roots of unity `k = 0..=27`; polynomials of up to 64 coefficients |
| `tests/kat_vectors.rs` | self-frozen | regression values of this crate's outputs, including the reference STARK |
| `tests/proptest_equiv.rs`, `tests/spec_tests.rs`, unit tests | self-consistency | field axioms, NTT round trips, FRI folding identity, Merkle round trips, prove/verify round trips and tamper rejection |

The Poseidon2 vector and the constants in `tests/plonky3_vectors.rs` were
copied byte for byte from the `p3-baby-bear` 0.5.2 crate on crates.io
(Plonky3 commit `3b3e175030dbd22770387eb9bf4f59e437fcab34`); both source files
are identical in 0.5.3. The Poseidon2 input was drawn with Sage
(`set_random_seed(16)`), and the expected output is the value recorded in
Plonky3's test. No other published test vectors for this instance were
found: the HorizenLabs repository publishes Baby Bear Poseidon2 vectors for
width 24 only, and for its own instance, and the Poseidon2 paper gives none.
The Plonky3 vector and the oracle cross-checks therefore both derive from
Plonky3; the field operations are in addition checked against identities
(Fermat, orders of the roots of unity, 7-th roots) that do not depend on any
implementation.

## Reference STARK

The modules `air`, `ntt`, `fri`, `quotient`, `ood`, `deep`, `pow`, `plonky3`
and `specs::merkle` implement a STARK over Baby Bear for the two-column
Fibonacci AIR. They are not Plonky3's prover, and their proofs are not
interoperable with Plonky3:

- `specs::merkle::hash_two_to_one` and `hash_leaf` are byte-wise mixing
  functions with no collision resistance;
- challenges and query indices are derived from commitment bytes by
  base-257 accumulation, not by a cryptographic transcript;
- the verifier does not check that the query indices in a proof are the
  derived ones.

These modules use `Vec`, slices and `Option`, and have no external test
vectors; their tests are self-consistency checks and the self-frozen values
in `tests/kat_vectors.rs`. The lib-level `Plonky3Crypto` trait and the
functions `p3_fold`, `p3_verify_constraint` and `p3_verify_opening` form a
small interface over them; `p3_verify_opening` compares a 32-byte prefix and
does not verify an opening.

## Running the tests

```sh
cargo test --release
cargo clippy --all-targets -- -D warnings
cargo doc --no-deps
```

The Kani harnesses in `src/kani.rs` run with `cargo kani`; the harnesses that
compare against `p3-baby-bear` need `cargo kani --features kani-equiv`. The
differential fuzz target in `fuzz/` is a standalone cargo-fuzz package:
`cargo +nightly fuzz run bb_equiv_p3`.

## hax extraction

`proofs/lean/extraction/Plonky3_hax.lean` is the Lean output of the hax Lean
backend for this crate. To regenerate the frontend export and the extraction
with a hax toolchain installed:

```sh
cargo hax json
cargo hax into lean
```

`hax_frontend_export.json` is the intermediate produced by the first command;
it is ignored by git.

## License

MIT; see `LICENSE`. The round constants and the matrix definitions are taken
from Plonky3, which is dual-licensed under MIT and Apache-2.0.
