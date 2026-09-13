//! Proof-of-work step of the reference STARK.
//!
//! Given a 32-byte `seed` and a difficulty `bits`, a nonce `n` is accepted
//! iff `hash_two_to_one(seed, nonce_to_hash(n))` has at least `bits` leading
//! zero bits (big-endian bit order), where `nonce_to_hash(n)` is `n` in
//! little-endian order in the first 8 bytes followed by 24 zero bytes. The
//! prover searches nonces in increasing order; for an ideal hash the
//! expected number of trials is `2^bits`. `hash_two_to_one` is the
//! non-cryptographic mixing function of `specs::merkle`.

use crate::specs::merkle::*;

/// Encode a `u64` nonce as a 32-byte hash input. Little-endian in the
/// low 8 bytes; remaining 24 bytes are zero.
fn nonce_to_hash(nonce: u64) -> MerkleHash {
    let mut out: MerkleHash = [0u8; HASH_SIZE];
    let mut n = nonce;
    for i in 0..8 {
        out[i] = (n & 0xff) as u8;
        n >>= 8;
    }
    out
}

/// Count the number of leading zero bits in a hash, big-endian.
///
/// Encoding choice: one `u32` state variable that holds either
/// `u32::MAX` ("haven't yet found a set bit") or the final answer.
/// Once a set bit is located the state does not change. The Lean
/// translation lifts one mutable variable per loop; two variables
/// (`count` and `done`) would need a tuple accumulator.
fn leading_zero_bits(h: &MerkleHash) -> u32 {
    const NOT_FOUND: u32 = u32::MAX;
    let mut result: u32 = NOT_FOUND;
    for i in 0..HASH_SIZE {
        if result == NOT_FOUND {
            let b = h[i];
            if b != 0 {
                for j in 0..8u32 {
                    if result == NOT_FOUND {
                        let mask = 1u8 << (7 - j);
                        if (b & mask) != 0 {
                            result = (i as u32) * 8 + j;
                        }
                    }
                }
            }
        }
    }
    if result == NOT_FOUND {
        (HASH_SIZE * 8) as u32
    } else {
        result
    }
}

/// Brute-force search for a nonce satisfying the PoW condition.
///
/// Returns the smallest `nonce ∈ [0, max_iter)` such that
/// `leading_zero_bits(hash_two_to_one(seed, nonce_to_hash(nonce))) ≥ bits`.
/// Returns `None` if no nonce in the range works.
///
/// `max_iter` caps the search to keep test runtimes bounded; in practice
/// the verifier's `bits` parameter is much smaller than `log2(max_iter)`,
/// so this loop always finds a nonce well before the cap.
pub fn grind_pow_nonce(seed: &MerkleHash, bits: u32, max_iter: u64) -> Option<u64> {
    if bits > 64 {
        return None;
    }
    for nonce in 0..max_iter {
        let h = hash_two_to_one(*seed, nonce_to_hash(nonce));
        if leading_zero_bits(&h) >= bits {
            return Some(nonce);
        }
    }
    None
}

/// Verifier-side PoW check: re-hash `(seed, nonce)` and confirm at least
/// `bits` leading zero bits.
pub fn verify_pow_nonce(seed: &MerkleHash, nonce: u64, bits: u32) -> bool {
    if bits > 64 {
        return false;
    }
    let h = hash_two_to_one(*seed, nonce_to_hash(nonce));
    leading_zero_bits(&h) >= bits
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leading_zero_bits_all_zero() {
        let h = [0u8; HASH_SIZE];
        assert_eq!(leading_zero_bits(&h), 256);
    }

    #[test]
    fn test_leading_zero_bits_high_byte() {
        // 0x80 = 10000000 — 0 leading zeros.
        let mut h = [0u8; HASH_SIZE];
        h[0] = 0x80;
        assert_eq!(leading_zero_bits(&h), 0);
        // 0x01 in byte 0 = 7 leading zeros.
        h[0] = 0x01;
        assert_eq!(leading_zero_bits(&h), 7);
        // 0x00 then 0x80 in byte 1 = 8 leading zeros.
        h[0] = 0x00;
        h[1] = 0x80;
        assert_eq!(leading_zero_bits(&h), 8);
    }

    #[test]
    fn test_grind_zero_bits_succeeds_immediately() {
        // bits = 0 always passes — nonce = 0 works.
        let seed = [0xAAu8; HASH_SIZE];
        let nonce = grind_pow_nonce(&seed, 0, 16).expect("zero-bit PoW must succeed");
        assert_eq!(nonce, 0);
        assert!(verify_pow_nonce(&seed, nonce, 0));
    }

    #[test]
    fn test_grind_and_verify_4_bits() {
        // Look for a 4-bit PoW. Expected to find within ~16 attempts.
        let seed = [0x33u8; HASH_SIZE];
        let nonce = grind_pow_nonce(&seed, 4, 1024).expect("4-bit PoW must succeed");
        assert!(verify_pow_nonce(&seed, nonce, 4));
        if nonce > 0 {
            // Nonce - 1 must NOT verify (else grind didn't return the smallest).
            assert!(!verify_pow_nonce(&seed, nonce - 1, 4));
        }
    }

    #[test]
    fn test_verify_rejects_insufficient_pow() {
        let seed = [0u8; HASH_SIZE];
        // Demand 32 bits; nonce = 0 almost certainly won't have 32 leading zeros.
        assert!(!verify_pow_nonce(&seed, 0, 32));
    }
}
