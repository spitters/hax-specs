//! AES-GCM (NIST SP 800-38D): AES-128/AES-256 and GHASH wired into GCM mode.
//!
//! Two layers:
//!   * [`RealGcm`] implements the `AesCipher` + `GcmCrypto` traits with
//!     the AES-128 and GHASH primitives of this crate, so that the
//!     fixed-shape `gcm::gcm_encrypt` / `gcm::gcm_decrypt` (64-byte PT,
//!     one AAD block) compute standard AES-128-GCM.
//!   * A variable-length GCM core ([`gcm_encrypt_var`] /
//!     [`gcm_decrypt_var`]) over byte slices supporting both AES-128 and
//!     AES-256, used by the NIST CAVP test vectors (16- and 32-byte
//!     plaintexts).
//!
//! hax-extraction note: the trait impls and the per-block primitives use
//! fixed `[u8; N]` arrays and bounded loops. The variable-length core uses
//! `&[u8]`/`&mut [u8]` slices with bounded `for i in 0..len` loops and no
//! `Vec`/`while`/`?`.

use crate::aes::AesCipher;
use crate::aes_impl::{aes128_encrypt_block, aes256_encrypt_block};
use crate::counter::{inc32, make_j0, xor_blocks};
use crate::ghash_impl::ghash_mul;
use crate::gcm::GcmCrypto;
use crate::types::{AesBlock, AesKey, GcmNonce, GcmState, GcmTag};

/// Concrete GCM backend over the AES-128 cipher and GHASH of this crate.
#[derive(Copy, Clone)]
pub struct RealGcm;

impl AesCipher for RealGcm {
    fn aes128_encrypt_block(self, key: &AesKey, block: &AesBlock) -> AesBlock {
        aes128_encrypt_block(key, block)
    }
}

impl GcmCrypto for RealGcm {
    fn ghash_multiply(self, h: &GcmState, x: &GcmState) -> GcmState {
        ghash_mul(h, x)
    }
}

// ---------------------------------------------------------------------------
// Variable-length GCM core (AES-128 and AES-256).
// ---------------------------------------------------------------------------

/// Which AES key size to use for the variable-length core.
#[derive(Copy, Clone)]
pub enum AesVariant {
    Aes128,
    Aes256,
}

/// Encrypt a block under the selected AES variant.
///
/// `key` must be 16 bytes for `Aes128` and 32 bytes for `Aes256`; only the
/// relevant prefix is read.
fn aes_encrypt_block(variant: AesVariant, key: &[u8; 32], block: &AesBlock) -> AesBlock {
    match variant {
        AesVariant::Aes128 => {
            let mut k: AesKey = [0u8; 16];
            for i in 0..16 {
                k[i] = key[i];
            }
            aes128_encrypt_block(&k, block)
        }
        AesVariant::Aes256 => aes256_encrypt_block(key, block),
    }
}

/// One GHASH absorb step: `state = (state XOR block) . H`.
fn ghash_step(h: &GcmState, state: &GcmState, block: &AesBlock) -> GcmState {
    let xored: GcmState = xor_blocks(state, block);
    ghash_mul(h, &xored)
}

/// Absorb a byte slice into the GHASH state, 16 bytes at a time, zero-padding
/// the final partial block on the right (NIST SP 800-38D Section 6.4).
fn ghash_absorb(h: &GcmState, state: &GcmState, data: &[u8]) -> GcmState {
    let mut acc: GcmState = *state;
    let len: usize = data.len();
    let full: usize = len / 16;
    for b in 0..full {
        let mut blk: AesBlock = [0u8; 16];
        for i in 0..16 {
            blk[i] = data[b * 16 + i];
        }
        acc = ghash_step(h, &acc, &blk);
    }
    let rem: usize = len % 16;
    if rem != 0 {
        let mut blk: AesBlock = [0u8; 16];
        for i in 0..rem {
            blk[i] = data[full * 16 + i];
        }
        acc = ghash_step(h, &acc, &blk);
    }
    acc
}

/// Encode two u64 bit-lengths into the GHASH length block.
fn make_len_block(aad_len: usize, ct_len: usize) -> AesBlock {
    let aad_bits: u64 = (aad_len as u64).wrapping_mul(8);
    let ct_bits: u64 = (ct_len as u64).wrapping_mul(8);
    let mut block: AesBlock = [0u8; 16];
    for i in 0..8 {
        block[i] = ((aad_bits >> (56 - 8 * i)) & 0xFF) as u8;
        block[8 + i] = ((ct_bits >> (56 - 8 * i)) & 0xFF) as u8;
    }
    block
}

/// Compute the GHASH over AAD then ciphertext then the length block.
fn ghash_full(h: &GcmState, aad: &[u8], ciphertext: &[u8]) -> GcmState {
    let zero: GcmState = [0u8; 16];
    let s1: GcmState = ghash_absorb(h, &zero, aad);
    let s2: GcmState = ghash_absorb(h, &s1, ciphertext);
    let len_block: AesBlock = make_len_block(aad.len(), ciphertext.len());
    ghash_step(h, &s2, &len_block)
}

/// CTR-mode keystream XOR over a slice, starting from counter `start`
/// (which is incremented *before* the first keystream block, matching
/// GCM's use of `inc32(J0)` for the first data block).
fn gctr(variant: AesVariant, key: &[u8; 32], start: &AesBlock, input: &[u8], output: &mut [u8]) {
    let len: usize = input.len();
    let full: usize = len / 16;
    let mut counter: AesBlock = *start;
    for b in 0..full {
        counter = inc32(&counter);
        let ks: AesBlock = aes_encrypt_block(variant, key, &counter);
        for i in 0..16 {
            output[b * 16 + i] = input[b * 16 + i] ^ ks[i];
        }
    }
    let rem: usize = len % 16;
    if rem != 0 {
        counter = inc32(&counter);
        let ks: AesBlock = aes_encrypt_block(variant, key, &counter);
        for i in 0..rem {
            output[full * 16 + i] = input[full * 16 + i] ^ ks[i];
        }
    }
}

/// Variable-length AES-GCM encryption (NIST SP 800-38D, 96-bit IV).
///
/// `key` holds the AES key (16 bytes for `Aes128`, 32 for `Aes256`).
/// Writes ciphertext into `ciphertext` (must equal `plaintext.len()`),
/// returns the 16-byte tag.
pub fn gcm_encrypt_var(
    variant: AesVariant,
    key: &[u8; 32],
    nonce: &GcmNonce,
    aad: &[u8],
    plaintext: &[u8],
    ciphertext: &mut [u8],
) -> GcmTag {
    // H = AES_K(0^128).
    let zero: AesBlock = [0u8; 16];
    let h: GcmState = aes_encrypt_block(variant, key, &zero);

    // J0 = nonce || 0x00000001.
    let j0: AesBlock = make_j0(nonce);

    // C = GCTR_K(inc32(J0), P).
    gctr(variant, key, &j0, plaintext, ciphertext);

    // S = GHASH_H(A || C || len).
    let s: GcmState = ghash_full(&h, aad, ciphertext);

    // T = S XOR AES_K(J0).
    let ej0: AesBlock = aes_encrypt_block(variant, key, &j0);
    let mut tag: GcmTag = [0u8; 16];
    for i in 0..16 {
        tag[i] = s[i] ^ ej0[i];
    }
    tag
}

/// Constant-time tag comparison.
fn tags_equal(a: &GcmTag, b: &GcmTag) -> bool {
    let mut acc: u8 = 0;
    for i in 0..16 {
        acc |= a[i] ^ b[i];
    }
    acc == 0
}

/// Variable-length AES-GCM decryption with tag verification.
///
/// On success writes plaintext into `plaintext` and returns `true`;
/// on tag mismatch leaves `plaintext` untouched and returns `false`.
pub fn gcm_decrypt_var(
    variant: AesVariant,
    key: &[u8; 32],
    nonce: &GcmNonce,
    aad: &[u8],
    ciphertext: &[u8],
    tag: &GcmTag,
    plaintext: &mut [u8],
) -> bool {
    let zero: AesBlock = [0u8; 16];
    let h: GcmState = aes_encrypt_block(variant, key, &zero);
    let j0: AesBlock = make_j0(nonce);

    let s: GcmState = ghash_full(&h, aad, ciphertext);
    let ej0: AesBlock = aes_encrypt_block(variant, key, &j0);
    let mut expected: GcmTag = [0u8; 16];
    for i in 0..16 {
        expected[i] = s[i] ^ ej0[i];
    }
    if !tags_equal(tag, &expected) {
        return false;
    }
    gctr(variant, key, &j0, ciphertext, plaintext);
    true
}
