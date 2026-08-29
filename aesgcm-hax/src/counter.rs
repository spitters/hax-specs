use crate::aes::AesCipher;
use crate::types::{AesBlock, AesKey, GcmNonce};

/// XOR two 16-byte blocks.
pub fn xor_blocks(a: &AesBlock, b: &AesBlock) -> AesBlock {
    let mut out: AesBlock = [0u8; 16];
    for i in 0..16 {
        out[i] = a[i] ^ b[i];
    }
    out
}

/// Construct J0 from a 96-bit nonce: J0 = nonce || 0x00000001.
///
/// Per NIST SP 800-38D Section 7.1, when the nonce is 96 bits,
/// the initial counter block is the nonce with a 32-bit counter
/// initialized to 1.
pub fn make_j0(nonce: &GcmNonce) -> AesBlock {
    let mut j0: AesBlock = [0u8; 16];
    for i in 0..12 {
        j0[i] = nonce[i];
    }
    j0[12] = 0x00;
    j0[13] = 0x00;
    j0[14] = 0x00;
    j0[15] = 0x01;
    j0
}

/// Increment the last 4 bytes of a block as a big-endian 32-bit counter.
///
/// Per NIST SP 800-38D Section 6.2, inc_32(X) increments the
/// rightmost 32 bits of X modulo 2^32, leaving the leftmost 96 bits
/// unchanged.
pub fn inc32(block: &AesBlock) -> AesBlock {
    let mut out: AesBlock = [0u8; 16];
    for i in 0..16 {
        out[i] = block[i];
    }
    // Increment the last 4 bytes as big-endian u32.
    // We do it byte-by-byte with carry propagation.
    let b15: u16 = (out[15] as u16) + 1;
    out[15] = (b15 & 0xFF) as u8;
    let carry: u16 = b15 >> 8;

    let b14: u16 = (out[14] as u16) + carry;
    out[14] = (b14 & 0xFF) as u8;
    let carry: u16 = b14 >> 8;

    let b13: u16 = (out[13] as u16) + carry;
    out[13] = (b13 & 0xFF) as u8;
    let carry: u16 = b13 >> 8;

    let b12: u16 = (out[12] as u16) + carry;
    out[12] = (b12 & 0xFF) as u8;
    // Carry out of byte 12 is discarded (modulo 2^32).

    out
}

/// Encrypt one block in counter (GCTR) mode.
///
/// GCTR_K(counter, input) = input XOR AES_K(counter).
pub fn gctr_one_block<C: AesCipher>(
    crypto: C,
    key: &AesKey,
    counter: &AesBlock,
    input: &AesBlock,
) -> AesBlock {
    let encrypted_counter: AesBlock = crypto.aes128_encrypt_block(key, counter);
    xor_blocks(input, &encrypted_counter)
}
