//! The Baby Bear prime field and the width-16 Poseidon2 permutation of
//! Plonky3 0.5, and a reference STARK built on the field, written in the
//! fragment of Rust that [hax](https://github.com/cryspen/hax) extracts.
//!
//! Modules that follow a published definition:
//!
//! - `specs::baby_bear`: arithmetic in F_p, p = 2^31 - 2^27 + 1, on
//!   canonical representatives (`p3-baby-bear` 0.5).
//! - `specs::poseidon2`: `default_babybear_poseidon2_16` of `p3-baby-bear`
//!   0.5.
//!
//! Modules of the reference STARK, which follow no published specification
//! and are not interoperable with Plonky3's prover:
//!
//! - `specs::merkle`: binary Merkle trees over a 32-byte non-cryptographic
//!   mixing function.
//! - `air`: execution traces, transition and boundary constraints, and the
//!   Fibonacci AIR.
//! - `ntt`: the radix-2 number-theoretic transform and its inverse.
//! - `fri`: FRI folding over Merkle-committed evaluations.
//! - `quotient`, `ood`, `deep`, `pow`: quotient polynomial, out-of-domain
//!   evaluation, DEEP quotients and proof-of-work.
//! - `plonky3`: prover and verifier composing the above.
//!
//! The trait `Plonky3Crypto` and the functions `p3_fold`,
//! `p3_verify_constraint` and `p3_verify_opening` are a small interface over
//! the same modules.
//!
//! References:
//! * Plonky3, <https://github.com/Plonky3/Plonky3>.
//! * L. Grassi, D. Khovratovich, M. Schofnegger, *Poseidon2: A Faster
//!   Version of the Poseidon Hash Function*, IACR ePrint 2023/323.
//! * E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed-Solomon
//!   Interactive Oracle Proofs of Proximity*, ICALP 2018.

// Indexed `for i in 0..N` loops, explicit copies, `%`-based divisibility and
// explicit `match`/`return` on `Option` are the fragment the hax Lean backend
// extracts; the iterator, slice and `?` rewrites clippy suggests fall outside it.
#![allow(
    clippy::needless_range_loop,
    clippy::manual_memcpy,
    clippy::manual_is_multiple_of,
    clippy::question_mark,
    clippy::if_same_then_else
)]

pub mod specs;
pub mod air;
pub mod fri;
pub mod ntt;
pub mod quotient;
pub mod ood;
pub mod pow;
pub mod deep;
pub mod plonky3;

#[cfg(kani)]
pub mod kani;

pub use air::*;
pub use fri::*;
pub use plonky3::*;
pub use specs::baby_bear::*;
pub use specs::merkle::*;

// -------------------------------------------------------------------------
// Interface over the field, the Merkle hash and FRI folding.
// -------------------------------------------------------------------------

/// A Baby Bear field element: a `u64` in `[0, BABY_BEAR_PRIME)`.
pub type P3Field = u64;

/// Merkle root commitment (32 bytes).
pub type P3Commitment = [u8; 32];

/// A 256-byte opening proof for `p3_verify_opening`.
pub type P3Proof = [u8; 256];

/// Field arithmetic and hashing used by the STARK.
///
/// `BabyBearPlonky3` instantiates it with `specs::baby_bear` and the
/// `specs::merkle` hash.
pub trait Plonky3Crypto {
    fn field_add(a: P3Field, b: P3Field) -> P3Field;
    fn field_mul(a: P3Field, b: P3Field) -> P3Field;
    fn field_inv(a: P3Field) -> P3Field;
    fn hash_compress(left: P3Commitment, right: P3Commitment) -> P3Commitment;
    fn merkle_commit(data: &[P3Field]) -> P3Commitment;
}

/// Default Baby Bear instantiation of `Plonky3Crypto`.
pub struct BabyBearPlonky3;

impl Plonky3Crypto for BabyBearPlonky3 {
    fn field_add(a: P3Field, b: P3Field) -> P3Field {
        bb_add(a, b)
    }
    fn field_mul(a: P3Field, b: P3Field) -> P3Field {
        bb_mul(a, b)
    }
    fn field_inv(a: P3Field) -> P3Field {
        bb_inv(a)
    }
    fn hash_compress(left: P3Commitment, right: P3Commitment) -> P3Commitment {
        hash_two_to_one(left, right)
    }
    fn merkle_commit(data: &[P3Field]) -> P3Commitment {
        let mut hashes: Vec<MerkleHash> = Vec::with_capacity(data.len());
        for i in 0..data.len() {
            hashes.push(hash_field_elem(data[i]));
        }
        // Round up to the next power of two and pad with the zero hash.
        // At most `usize::BITS` doublings are needed.
        let mut n: usize = 1;
        for _ in 0..(usize::BITS as usize) {
            if n >= data.len() {
                break;
            }
            n <<= 1;
        }
        let pad_to = n;
        let cur = hashes.len();
        for _ in cur..pad_to {
            hashes.push([0u8; HASH_SIZE]);
        }
        merkle_build_root(&hashes, n)
    }
}

/// FRI folding step at the point `x = 1`: `fri::fri_fold(f_pos, f_neg, 1, alpha)`.
pub fn p3_fold(f_pos: P3Field, f_neg: P3Field, alpha: P3Field) -> P3Field {
    crate::fri::fri_fold(f_pos, f_neg, 1, alpha)
}

/// Constraint verification: succeeds iff the evaluation equals the
/// expected value.
pub fn p3_verify_constraint(c_eval: P3Field, expected: P3Field) -> bool {
    c_eval == expected
}

/// Returns `true` iff the first 32 bytes of `proof` equal `commitment`.
///
/// The point and the claimed evaluation are not checked; this function is
/// not an opening verifier. Openings of the STARK are checked by
/// [`fri::fri_verify`] and [`specs::merkle::merkle_verify_path`].
pub fn p3_verify_opening(
    commitment: &P3Commitment,
    _point: P3Field,
    _claimed_eval: P3Field,
    proof: &P3Proof,
) -> bool {
    for i in 0..32 {
        if proof[i] != commitment[i] {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod interface_tests {
    use super::*;

    #[test]
    fn test_baby_bear_trait_impl_field() {
        let a: P3Field = 12345;
        let b: P3Field = 67890;
        assert_eq!(
            BabyBearPlonky3::field_add(a, b),
            bb_add(a, b)
        );
        assert_eq!(
            BabyBearPlonky3::field_mul(a, b),
            bb_mul(a, b)
        );
        assert_eq!(
            BabyBearPlonky3::field_mul(a, BabyBearPlonky3::field_inv(a)),
            1
        );
    }

    #[test]
    fn test_p3_fold_at_one() {
        // At x = 1: fold = (f_pos + f_neg)/2 + alpha*(f_pos - f_neg)/2
        let f_pos: P3Field = 100;
        let f_neg: P3Field = 50;
        let alpha: P3Field = 3;
        let result = p3_fold(f_pos, f_neg, alpha);
        // Compute expected manually via bb ops
        let sum = bb_add(f_pos, f_neg);
        let diff = bb_sub(f_pos, f_neg);
        let inv_two = bb_inv(2);
        let expected = bb_add(bb_mul(sum, inv_two), bb_mul(alpha, bb_mul(diff, inv_two)));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_p3_verify_constraint() {
        assert!(p3_verify_constraint(0, 0));
        assert!(p3_verify_constraint(42, 42));
        assert!(!p3_verify_constraint(1, 0));
    }

    #[test]
    fn test_p3_verify_opening_prefix() {
        let commitment: P3Commitment = [0xAB; 32];
        let mut proof: P3Proof = [0u8; 256];
        proof[..32].copy_from_slice(&commitment);
        assert!(p3_verify_opening(&commitment, 7, 99, &proof));
        proof[0] = 0x00;
        assert!(!p3_verify_opening(&commitment, 7, 99, &proof));
    }

    #[test]
    fn test_merkle_commit_trait() {
        let data = [1u64, 2, 3, 4];
        let commit1 = BabyBearPlonky3::merkle_commit(&data);
        let commit2 = BabyBearPlonky3::merkle_commit(&data);
        assert_eq!(commit1, commit2, "merkle_commit is deterministic");

        let data2 = [1u64, 2, 3, 5];
        let commit3 = BabyBearPlonky3::merkle_commit(&data2);
        assert_ne!(commit1, commit3, "different inputs -> different roots");
    }
}
