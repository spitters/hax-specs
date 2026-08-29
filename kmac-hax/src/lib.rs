//! KMAC: Hax-extractable implementation (NIST SP 800-185, Section 8).
//!
//! This crate implements the KMAC encoding layer (left_encode, right_encode,
//! encode_string, bytepad) and the top-level KMAC-128/256 construction in a
//! style suitable for hax extraction to Lean 4.
//!
//! All loops are bounded `for i in 0..N` (no `while`), all arithmetic is
//! wrapping, and all buffers are fixed-size arrays.
//!
//! SP 800-185 construction:
//!   KMAC(K, X, L, S) = cSHAKE(bytepad(encode_string(K), w) || X || right_encode(L),
//!                              L, "KMAC", S)
//!
//! `keccak` holds the FIPS 202 Keccak-f\[1600\] sponge; `kmac128` and `kmac256`
//! evaluate the full construction over it.

// Index-driven `for i in 0..N` loops and explicit `% w` tests are the loop and
// arithmetic forms hax extracts; the slice-copy and `is_multiple_of` rewrites are not.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy, clippy::manual_is_multiple_of)]

pub mod keccak;

// ---------------------------------------------------------------------------
// Encoding result types
// ---------------------------------------------------------------------------

/// Result of left_encode or right_encode: up to 9 bytes (1 byte count + 8 value bytes).
/// `len` is the number of valid bytes in `data`.
#[derive(Clone, Copy)]
pub struct Encoded9 {
    pub data: [u8; 9],
    pub len: usize,
}

/// Result of encode_string: up to 9 + KEY_MAX bytes.
/// We use 41 = 9 (left_encode) + 32 (max key bytes for KMAC-256).
/// `len` is the number of valid bytes in `data`.
#[derive(Clone, Copy)]
pub struct Encoded41 {
    pub data: [u8; 41],
    pub len: usize,
}

// ---------------------------------------------------------------------------
// Byte-counting helper
// ---------------------------------------------------------------------------

/// Count the number of bytes needed to represent `x` in big-endian.
/// Returns 1 for x == 0 (the spec encodes 0 as a single zero byte).
/// Uses a bounded for-loop instead of while for hax compatibility.
fn byte_count(x: usize) -> u8 {
    if x == 0 {
        return 1;
    }
    let mut n: u8 = 0;
    // A usize is at most 8 bytes (64-bit). We iterate over each byte position
    // and check whether any bits remain at that position.
    for i in 0u8..8u8 {
        // If x >> (8 * i) > 0, then byte position i is needed.
        // We accumulate the highest such position + 1.
        let shift = (i as u32).wrapping_mul(8);
        if shift < 64 {
            let shifted = x >> (shift as usize);
            if shifted > 0 {
                n = i.wrapping_add(1);
            }
        }
    }
    n
}

// ---------------------------------------------------------------------------
// left_encode (SP 800-185, Section 2.3.1)
// ---------------------------------------------------------------------------

/// Left-encode an integer x.
///
/// Encoding: `n || x_1 || x_2 || ... || x_n`
/// where n is the number of bytes needed to represent x (big-endian).
pub fn left_encode(x: usize) -> Encoded9 {
    let mut out = [0u8; 9];
    let n = byte_count(x);
    out[0] = n;

    // Fill big-endian bytes into positions 1..=n.
    // Byte at position 1 is the most significant, position n is the least.
    for i in 0u8..8u8 {
        if i < n {
            // Byte index in the output: n - i (counting from MSB)
            let out_idx = (n.wrapping_sub(i)) as usize;
            // Extract the i-th least-significant byte of x
            let shift = (i as u32).wrapping_mul(8);
            let byte_val = if shift < 64 {
                ((x >> (shift as usize)) & 0xFF) as u8
            } else {
                0u8
            };
            out[out_idx] = byte_val;
        }
    }

    Encoded9 {
        data: out,
        len: (n as usize).wrapping_add(1), // n bytes of value + 1 byte of count
    }
}

// ---------------------------------------------------------------------------
// right_encode (SP 800-185, Section 2.3.1)
// ---------------------------------------------------------------------------

/// Right-encode an integer x.
///
/// Encoding: `x_1 || x_2 || ... || x_n || n`
/// where n is the number of bytes needed to represent x (big-endian).
pub fn right_encode(x: usize) -> Encoded9 {
    let mut out = [0u8; 9];
    let n = byte_count(x);

    // Fill big-endian bytes into positions 0..n-1.
    // Position 0 is most significant, position n-1 is least significant.
    for i in 0u8..8u8 {
        if i < n {
            // Byte index in the output: (n - 1) - i (counting from MSB)
            let out_idx = (n.wrapping_sub(1).wrapping_sub(i)) as usize;
            // Extract the i-th least-significant byte of x
            let shift = (i as u32).wrapping_mul(8);
            let byte_val = if shift < 64 {
                ((x >> (shift as usize)) & 0xFF) as u8
            } else {
                0u8
            };
            out[out_idx] = byte_val;
        }
    }

    // Append the byte count at position n
    out[n as usize] = n;

    Encoded9 {
        data: out,
        len: (n as usize).wrapping_add(1), // n bytes of value + 1 byte of count
    }
}

// ---------------------------------------------------------------------------
// encode_string (SP 800-185, Section 2.3.2)
// ---------------------------------------------------------------------------

/// Encode a byte string of up to 32 bytes.
///
/// `encode_string(S) = left_encode(len(S) * 8) || S`
///
/// The length argument is in bits (hence * 8).
/// Buffer is 41 bytes: up to 9 for left_encode + up to 32 for the string.
pub fn encode_string_32(s: &[u8; 32], s_len: usize) -> Encoded41 {
    let mut out = [0u8; 41];

    // Compute bit length (wrapping, for hax)
    let bit_len = s_len.wrapping_mul(8);
    let le = left_encode(bit_len);

    // Copy left_encode output (up to 9 bytes)
    for i in 0usize..9usize {
        if i < le.len {
            out[i] = le.data[i];
        }
    }

    // Copy string bytes after the left_encode prefix
    let offset = le.len;
    for j in 0usize..32usize {
        if j < s_len {
            let dst = offset.wrapping_add(j);
            if dst < 41 {
                out[dst] = s[j];
            }
        }
    }

    Encoded41 {
        data: out,
        len: offset.wrapping_add(s_len),
    }
}

// ---------------------------------------------------------------------------
// bytepad (SP 800-185, Section 2.3.3)
// ---------------------------------------------------------------------------

/// Bytepad X to a w-byte boundary.
///
/// `bytepad(X, w) = left_encode(w) || X || 0*`
/// where `0*` pads to the next multiple of `w` bytes.
///
/// Returns a 168-byte buffer (KMAC-128 rate). For KMAC-256 (rate 136),
/// only the first 136 bytes are meaningful.
pub fn bytepad(x_data: &[u8; 41], x_len: usize, w: usize) -> [u8; 168] {
    let mut out = [0u8; 168];
    let le_w = left_encode(w);

    // Copy left_encode(w) into the output
    for i in 0usize..9usize {
        if i < le_w.len {
            out[i] = le_w.data[i];
        }
    }

    // Copy X after left_encode(w)
    let offset = le_w.len;
    for j in 0usize..41usize {
        if j < x_len {
            let dst = offset.wrapping_add(j);
            if dst < 168 {
                out[dst] = x_data[j];
            }
        }
    }

    // Remaining bytes are already zero (zero-padding to w-byte boundary)
    out
}

// ---------------------------------------------------------------------------
// KMAC-128 (SP 800-185, Section 8)
// ---------------------------------------------------------------------------

/// The three components of the KMAC cSHAKE input, in order:
/// `padded_key || data || right_enc_l`.
#[derive(Clone, Copy)]
pub struct KmacPreimage {
    /// bytepad(encode_string(K), 168) = 168 bytes
    pub padded_key: [u8; 168],
    /// input data
    pub data: [u8; 64],
    /// right_encode(L) where L is output length in bits
    pub right_enc_l: Encoded9,
}

/// Assemble the cSHAKE-128 input for KMAC-128.
///
/// KMAC128(K, X, L, S) =
///   cSHAKE128(bytepad(encode_string(K), 168) || X || right_encode(L),
///             L, "KMAC", S)
///
/// This function constructs the pre-image bytes that feed into cSHAKE-128.
/// The actual sponge evaluation is abstracted (requires Keccak).
///
/// Parameters:
/// - `key`: 32-byte KMAC key (256-bit)
/// - `data`: 64-byte input message
/// - `out_bits`: desired output length in bits (e.g. 256)
///
/// Returns the components
///   bytepad(encode_string(K), 168) || data || right_encode(out_bits)
/// as a `KmacPreimage`.
pub fn kmac128_preimage(key: &[u8; 32], data: &[u8; 64], out_bits: usize) -> KmacPreimage {
    // Step 1: encode_string(K) with full 32-byte key
    let encoded_key = encode_string_32(key, 32);

    // Step 2: bytepad(encode_string(K), 168) — SHAKE-128 rate
    let padded_key = bytepad(&encoded_key.data, encoded_key.len, 168);

    // Step 3: right_encode(L) where L = out_bits
    let re_l = right_encode(out_bits);

    // The full cSHAKE-128 input is: padded_key || data || re_l
    // with function name N = "KMAC" and customization string S.
    KmacPreimage {
        padded_key,
        data: *data,
        right_enc_l: re_l,
    }
}

// ---------------------------------------------------------------------------
// KMAC-256 (SP 800-185, Section 8)
// ---------------------------------------------------------------------------

/// Assemble the cSHAKE-256 input for KMAC-256.
///
/// Same as KMAC-128 but uses cSHAKE-256 (rate 136) instead of
/// cSHAKE-128 (rate 168).
pub fn kmac256_preimage(key: &[u8; 32], data: &[u8; 64], out_bits: usize) -> KmacPreimage {
    // Step 1: encode_string(K) with full 32-byte key
    let encoded_key = encode_string_32(key, 32);

    // Step 2: bytepad(encode_string(K), 136) — SHAKE-256 rate
    let padded_key = bytepad(&encoded_key.data, encoded_key.len, 136);

    // Step 3: right_encode(L) where L = out_bits
    let re_l = right_encode(out_bits);

    KmacPreimage {
        padded_key,
        data: *data,
        right_enc_l: re_l,
    }
}

// ---------------------------------------------------------------------------
// Real cSHAKE + KMAC over the Keccak sponge (SP 800-185, Sections 3 & 4)
// ---------------------------------------------------------------------------
//
// The functions above assemble the fixed-array preimage in a hax-extractable
// style. The functions below evaluate the full construction — including the
// cSHAKE sponge — for arbitrary-length keys, messages, and customization
// strings, so the crate's own `kmac128`/`kmac256` produce the SP 800-185 MAC.

/// left_encode(x): `n || x_1 || ... || x_n`, big-endian, minimal byte count
/// (n >= 1). SP 800-185 Section 2.3.1.
fn le_encode(x: u64) -> Vec<u8> {
    let bytes = x.to_be_bytes();
    let mut start = 0usize;
    while start < 7 && bytes[start] == 0 {
        start += 1;
    }
    let val = &bytes[start..];
    let mut out = Vec::with_capacity(val.len() + 1);
    out.push(val.len() as u8);
    out.extend_from_slice(val);
    out
}

/// right_encode(x): `x_1 || ... || x_n || n`, big-endian, minimal byte count
/// (n >= 1). SP 800-185 Section 2.3.1.
fn re_encode(x: u64) -> Vec<u8> {
    let bytes = x.to_be_bytes();
    let mut start = 0usize;
    while start < 7 && bytes[start] == 0 {
        start += 1;
    }
    let mut out = bytes[start..].to_vec();
    out.push((8 - start) as u8);
    out
}

/// encode_string(S) = left_encode(8 * len(S)) || S. SP 800-185 Section 2.3.2.
fn enc_string(s: &[u8]) -> Vec<u8> {
    let mut out = le_encode((s.len() as u64) * 8);
    out.extend_from_slice(s);
    out
}

/// bytepad(X, w) = left_encode(w) || X || 0*, zero-padded to a multiple of `w`.
/// SP 800-185 Section 2.3.3.
fn byte_pad(x: &[u8], w: usize) -> Vec<u8> {
    let mut out = le_encode(w as u64);
    out.extend_from_slice(x);
    while out.len() % w != 0 {
        out.push(0);
    }
    out
}

/// cSHAKE with function-name `n` and customization string `s`, at the given
/// byte `rate` (168 for the 128-bit strength, 136 for 256-bit).
///
/// cSHAKE(X, L, N, S) = KECCAK[c](bytepad(encode_string(N) || encode_string(S), rate)
///                                || X || 00, L)  when N or S is non-empty.
/// SP 800-185 Section 3.3. The trailing "00" domain-separation bits become the
/// 0x04 sponge delimiter.
fn cshake(rate: usize, x: &[u8], n: &[u8], s: &[u8], out: &mut [u8]) {
    let mut prefix = enc_string(n);
    prefix.extend_from_slice(&enc_string(s));
    let mut input = byte_pad(&prefix, rate);
    input.extend_from_slice(x);
    keccak::keccak(rate, 0x04, &input, out);
}

/// Assemble the KMAC message `newX = bytepad(encode_string(K), rate) || X ||
/// right_encode(8 * out_len)`. SP 800-185 Section 4.3.1.
fn kmac_newx(key: &[u8], data: &[u8], rate: usize, out_len: usize) -> Vec<u8> {
    let mut newx = byte_pad(&enc_string(key), rate);
    newx.extend_from_slice(data);
    newx.extend_from_slice(&re_encode((out_len as u64) * 8));
    newx
}

/// KMAC128 (SP 800-185 Section 4.3.1): cSHAKE128 at rate 168 with N = "KMAC".
/// `out.len()` bytes of tag are produced; `s` is the customization string.
pub fn kmac128(key: &[u8], data: &[u8], out: &mut [u8], s: &[u8]) {
    let newx = kmac_newx(key, data, 168, out.len());
    cshake(168, &newx, b"KMAC", s, out);
}

/// KMAC256 (SP 800-185 Section 4.3.1): cSHAKE256 at rate 136 with N = "KMAC".
/// `out.len()` bytes of tag are produced; `s` is the customization string.
pub fn kmac256(key: &[u8], data: &[u8], out: &mut [u8], s: &[u8]) {
    let newx = kmac_newx(key, data, 136, out.len());
    cshake(136, &newx, b"KMAC", s, out);
}

// ---------------------------------------------------------------------------
// Tests (not extracted by hax)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_count() {
        assert_eq!(byte_count(0), 1);
        assert_eq!(byte_count(1), 1);
        assert_eq!(byte_count(255), 1);
        assert_eq!(byte_count(256), 2);
        assert_eq!(byte_count(65535), 2);
        assert_eq!(byte_count(65536), 3);
    }

    #[test]
    fn test_left_encode_zero() {
        let enc = left_encode(0);
        assert_eq!(enc.len, 2); // 1 count byte + 1 value byte
        assert_eq!(enc.data[0], 1); // 1 byte needed
        assert_eq!(enc.data[1], 0); // value = 0
    }

    #[test]
    fn test_left_encode_small() {
        // left_encode(256) should produce [2, 1, 0]
        // n = 2 bytes needed, big-endian 256 = 0x01 0x00
        let enc = left_encode(256);
        assert_eq!(enc.len, 3); // 1 count byte + 2 value bytes
        assert_eq!(enc.data[0], 2); // 2 bytes needed
        assert_eq!(enc.data[1], 1); // 256 >> 8 = 1
        assert_eq!(enc.data[2], 0); // 256 & 0xFF = 0
    }

    #[test]
    fn test_left_encode_one() {
        let enc = left_encode(1);
        assert_eq!(enc.len, 2);
        assert_eq!(enc.data[0], 1); // 1 byte needed
        assert_eq!(enc.data[1], 1); // value = 1
    }

    #[test]
    fn test_left_encode_255() {
        let enc = left_encode(255);
        assert_eq!(enc.len, 2);
        assert_eq!(enc.data[0], 1); // 1 byte needed
        assert_eq!(enc.data[1], 255);
    }

    #[test]
    fn test_right_encode_zero() {
        let enc = right_encode(0);
        assert_eq!(enc.len, 2);
        assert_eq!(enc.data[0], 0); // value = 0
        assert_eq!(enc.data[1], 1); // 1 byte needed
    }

    #[test]
    fn test_right_encode_small() {
        // right_encode(256) should produce [1, 0, 2]
        // big-endian 256 = 0x01 0x00, then n = 2
        let enc = right_encode(256);
        assert_eq!(enc.len, 3);
        assert_eq!(enc.data[0], 1); // MSB of 256
        assert_eq!(enc.data[1], 0); // LSB of 256
        assert_eq!(enc.data[2], 2); // 2 bytes needed
    }

    #[test]
    fn test_right_encode_one() {
        let enc = right_encode(1);
        assert_eq!(enc.len, 2);
        assert_eq!(enc.data[0], 1); // value = 1
        assert_eq!(enc.data[1], 1); // 1 byte needed
    }

    #[test]
    fn test_encode_string_empty() {
        // encode_string of 0-length string:
        //   left_encode(0 * 8) = left_encode(0) = [1, 0]
        //   then 0 bytes of string
        let s = [0u8; 32];
        let enc = encode_string_32(&s, 0);
        assert_eq!(enc.len, 2); // just left_encode(0)
        assert_eq!(enc.data[0], 1); // left_encode byte count
        assert_eq!(enc.data[1], 0); // left_encode value
    }

    #[test]
    fn test_encode_string_four_bytes() {
        // encode_string of 4-byte string "KMAC" (ascii):
        //   len = 4, bit_len = 32 = 0x20
        //   left_encode(32) = [1, 32] (1 byte needed for 32)
        //   then the 4 bytes of "KMAC"
        let mut s = [0u8; 32];
        s[0] = b'K';
        s[1] = b'M';
        s[2] = b'A';
        s[3] = b'C';
        let enc = encode_string_32(&s, 4);
        assert_eq!(enc.len, 6); // 2 (left_encode) + 4 (string)
        assert_eq!(enc.data[0], 1); // left_encode: 1 byte needed
        assert_eq!(enc.data[1], 32); // left_encode: value = 32 (4*8 bits)
        assert_eq!(enc.data[2], b'K');
        assert_eq!(enc.data[3], b'M');
        assert_eq!(enc.data[4], b'A');
        assert_eq!(enc.data[5], b'C');
    }

    #[test]
    fn test_bytepad_starts_with_left_encode_w() {
        let x = Encoded41 {
            data: [0u8; 41],
            len: 0,
        };
        let result = bytepad(&x.data, x.len, 168);
        // left_encode(168): 168 = 0xA8, 1 byte needed
        // so [1, 168, 0, 0, ...]
        assert_eq!(result[0], 1);
        assert_eq!(result[1], 168);
    }

    #[test]
    fn test_bytepad_length_is_multiple_of_w() {
        // bytepad output is always 168 bytes (our fixed buffer size),
        // and 168 is a multiple of 168.
        let x = Encoded41 {
            data: [0u8; 41],
            len: 0,
        };
        let result = bytepad(&x.data, x.len, 168);
        assert_eq!(result.len(), 168);
    }

    #[test]
    fn test_kmac128_preimage_structure() {
        let key = [0xABu8; 32];
        let data = [0xCDu8; 64];
        let pre = kmac128_preimage(&key, &data, 256);

        // padded_key should start with left_encode(168) = [1, 168]
        assert_eq!(pre.padded_key[0], 1);
        assert_eq!(pre.padded_key[1], 168);

        // data should be preserved
        assert_eq!(pre.data, [0xCDu8; 64]);

        // right_encode(256): 256 = 0x0100, 2 bytes, so [1, 0, 2]
        assert_eq!(pre.right_enc_l.data[0], 1);
        assert_eq!(pre.right_enc_l.data[1], 0);
        assert_eq!(pre.right_enc_l.data[2], 2);
        assert_eq!(pre.right_enc_l.len, 3);
    }

    #[test]
    fn test_kmac256_preimage_uses_rate_136() {
        let key = [0u8; 32];
        let data = [0u8; 64];
        let pre = kmac256_preimage(&key, &data, 512);

        // padded_key should start with left_encode(136) = [1, 136]
        assert_eq!(pre.padded_key[0], 1);
        assert_eq!(pre.padded_key[1], 136);
    }

    // SP 800-185 test vector validation (Section 8, Sample #1):
    // KMAC128 with:
    //   Key  = 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F
    //          50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F
    //   Data = 00 01 02 03
    //   L    = 256 bits
    //   S    = "" (empty customization)
    //
    // The encoding layer produces:
    //   encode_string(K): left_encode(256) || K
    //     = [02, 01, 00, 40, 41, ..., 5F]  (2 + 32 = 34 bytes)
    //   bytepad(encode_string(K), 168): 168 bytes
    //   right_encode(256) = [01, 00, 02]
    #[test]
    fn test_sp800_185_sample1_encoding() {
        let mut key = [0u8; 32];
        for i in 0u8..32u8 {
            key[i as usize] = 0x40u8.wrapping_add(i);
        }

        let encoded = encode_string_32(&key, 32);
        // bit_len = 32 * 8 = 256 = 0x0100
        // left_encode(256) = [2, 1, 0]  (2 bytes needed for 256)
        assert_eq!(encoded.data[0], 2); // byte count = 2
        assert_eq!(encoded.data[1], 1); // MSB of 256
        assert_eq!(encoded.data[2], 0); // LSB of 256
        assert_eq!(encoded.data[3], 0x40); // first key byte
        assert_eq!(encoded.len, 35); // 3 + 32

        let padded = bytepad(&encoded.data, encoded.len, 168);
        // left_encode(168) = [1, 168]
        assert_eq!(padded[0], 1);
        assert_eq!(padded[1], 168);
        // Then encode_string(K) follows at offset 2
        assert_eq!(padded[2], 2); // byte count from encode_string
        assert_eq!(padded[3], 1); // MSB of 256
        assert_eq!(padded[4], 0); // LSB of 256
        assert_eq!(padded[5], 0x40); // first key byte
    }
}
