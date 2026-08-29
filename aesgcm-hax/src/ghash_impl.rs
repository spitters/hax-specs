//! GHASH GF(2^128) multiplication (NIST SP 800-38D, Section 6.3).
//!
//! Implements the standard right-shift / `R = 0xe1...` reduction over the
//! GCM field GF(2^128) with the polynomial x^128 + x^7 + x^2 + x + 1.
//! The bit ordering follows the GCM convention: within each 16-byte block,
//! byte 0 is the most significant and, within a byte, bit 7 (0x80) is the
//! most significant (i.e. corresponds to the field element 1).
//!
//! hax-extraction-friendly: fixed `[u8; 16]` arrays, bounded loops, only
//! shifts/xor, no `Vec`/`while`/`?`.

use crate::types::GcmState;

/// Shift a 128-bit big-endian value (as `[u8; 16]`) right by one bit.
fn shift_right_1(v: &GcmState) -> GcmState {
    let mut out: GcmState = [0u8; 16];
    let mut carry: u8 = 0;
    for i in 0..16 {
        let cur: u8 = v[i];
        out[i] = (cur >> 1) | (carry << 7);
        carry = cur & 1;
    }
    out
}

/// Test bit `bit` (0 = MSB of byte 0 ... 127 = LSB of byte 15) of a block.
///
/// Returns `1` if set, `0` otherwise. In the GCM convention this walks the
/// field-coefficient order from the most significant bit downward.
fn get_bit(v: &GcmState, bit: usize) -> u8 {
    let byte: usize = bit / 8;
    let within: usize = bit % 8;
    // within = 0 -> MSB (0x80).
    let shift: u8 = (7 - within) as u8;
    (v[byte] >> shift) & 1
}

/// XOR two 16-byte blocks.
fn xor16(a: &GcmState, b: &GcmState) -> GcmState {
    let mut out: GcmState = [0u8; 16];
    for i in 0..16 {
        out[i] = a[i] ^ b[i];
    }
    out
}

/// Multiply two field elements in GF(2^128) per the GCM convention.
///
/// Computes `Z = X . Y` using Algorithm 1 of SP 800-38D: scan the bits of
/// `x` from most significant to least significant; on each set bit add the
/// running multiple of `y`, then multiply `y` by the field generator (a
/// right shift with conditional `R = 0xe1<<120` reduction).
pub fn ghash_mul(x: &GcmState, y: &GcmState) -> GcmState {
    let mut z: GcmState = [0u8; 16];
    let mut v: GcmState = *y;
    for i in 0..128 {
        if get_bit(x, i) == 1 {
            z = xor16(&z, &v);
        }
        // v = v >> 1, then if the bit shifted out (old LSB) was 1, XOR R.
        let lsb: u8 = v[15] & 1;
        v = shift_right_1(&v);
        if lsb == 1 {
            // R = 1110_0001 || 0^120 = 0xe1 in the top byte.
            v[0] ^= 0xe1;
        }
    }
    z
}

/// Concrete GHASH multiply matching the `GcmCrypto::ghash_multiply`
/// signature `(h, x) -> h . x`.
pub fn ghash_multiply(h: &GcmState, x: &GcmState) -> GcmState {
    ghash_mul(h, x)
}
