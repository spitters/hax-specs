//! Cryptographic primitive specifications for Plonky3.
//!
//! These modules provide pure, hax-extractable functions for:
//! - `baby_bear`: Baby Bear prime field arithmetic (p = 2^31 - 2^27 + 1)
//! - `merkle`: Merkle tree commitment and authentication-path verification
//! - `poseidon2`: Width-16 Poseidon2 permutation (Plonky3 standard hash)

pub mod baby_bear;
pub mod merkle;
pub mod poseidon2;
