// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! CTR_DRBG with AES-128 and no derivation function (NIST SP 800-90A Rev. 1,
//! Section 10.2.1), in the Rust subset accepted by hax.
//!
//! CTR_DRBG uses AES-128 in counter mode as the underlying block cipher.
//! For AES-128: blocklen = 128 bits = 16 bytes, keylen = 128 bits = 16 bytes,
//! seedlen = keylen + blocklen = 256 bits = 32 bytes.
//!
//! State: (Key: [u8; 16], V: [u8; 16])
//!
//! Operations:
//!   - Update: refresh Key and V from provided_data
//!   - Instantiate: set initial state from entropy and personalization
//!   - Generate: produce pseudorandom blocks and update state
//!   - Reseed: refresh state from new entropy
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays.

#![no_std]
// The hax-extractable loop form indexes arrays with a bounded `for i in 0..N`.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

// =========================================================================
// AES-128 specification (FIPS 197); the same code as in the cmac-hax crate
// =========================================================================

/// AES S-box lookup table (FIPS 197, Figure 7).
pub static AES_SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

/// AES round constants (FIPS 197, Section 5.2).
static RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

/// A 128-bit block (16 bytes).
pub type Block = [u8; 16];

/// AES-128 key: 16 bytes.
pub type AesKey = [u8; 16];

/// AES-128 round keys: 11 x 16 bytes (initial + 10 rounds).
pub type RoundKeys = [[u8; 16]; 11];

/// Zero block constant.
pub const ZERO_BLOCK: Block = [0u8; 16];

/// Seed length for AES-128 CTR_DRBG: keylen + blocklen = 32 bytes.
pub const SEEDLEN: usize = 32;

/// Maximum number of blocks that can be generated in a single call.
pub const MAX_GEN_BLOCKS: usize = 16;

// =========================================================================
// Block operations
// =========================================================================

/// XOR two 128-bit blocks.
#[inline]
pub fn xor_block(a: &Block, b: &Block) -> Block {
    let mut result: Block = [0u8; 16];
    for i in 0..16 {
        result[i] = a[i] ^ b[i];
    }
    result
}

// =========================================================================
// AES-128 key expansion (FIPS 197, Section 5.2)
// =========================================================================

/// Multiply by 2 in GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1.
#[inline]
fn gf_mul2(x: u8) -> u8 {
    let shifted = (x as u16) << 1;
    let reduced = if x & 0x80 != 0 { shifted ^ 0x1b } else { shifted };
    reduced as u8
}

/// Multiply by 3 in GF(2^8): 3*x = 2*x XOR x.
#[inline]
fn gf_mul3(x: u8) -> u8 {
    gf_mul2(x) ^ x
}

/// AES SubBytes on a single word (4 bytes).
#[inline]
fn sub_word(w: [u8; 4]) -> [u8; 4] {
    [AES_SBOX[w[0] as usize], AES_SBOX[w[1] as usize],
     AES_SBOX[w[2] as usize], AES_SBOX[w[3] as usize]]
}

/// AES RotWord: rotate 4 bytes left by 1.
#[inline]
fn rot_word(w: [u8; 4]) -> [u8; 4] {
    [w[1], w[2], w[3], w[0]]
}

/// AES-128 key expansion: produce 11 round keys from 16-byte key.
pub fn aes128_key_expansion(key: &AesKey) -> RoundKeys {
    let mut rk: RoundKeys = [[0u8; 16]; 11];

    // Copy initial key into first round key
    for i in 0..16 {
        rk[0][i] = key[i];
    }

    // Expand: for each subsequent word W[i] (i = 4..43)
    for round in 1..11 {
        let prev_last: [u8; 4] = [
            rk[round - 1][12], rk[round - 1][13],
            rk[round - 1][14], rk[round - 1][15],
        ];

        let rotated = rot_word(prev_last);
        let subbed = sub_word(rotated);
        let rcon_byte = RCON[round - 1];

        rk[round][0] = rk[round - 1][0] ^ subbed[0] ^ rcon_byte;
        rk[round][1] = rk[round - 1][1] ^ subbed[1];
        rk[round][2] = rk[round - 1][2] ^ subbed[2];
        rk[round][3] = rk[round - 1][3] ^ subbed[3];

        for j in 1..4 {
            let base = j * 4;
            for b in 0..4 {
                rk[round][base + b] = rk[round - 1][base + b] ^ rk[round][base - 4 + b];
            }
        }
    }

    rk
}

// =========================================================================
// AES-128 single-block encryption (FIPS 197)
// =========================================================================

/// AES SubBytes: apply S-box to all 16 bytes.
fn aes_sub_bytes(state: &mut Block) {
    for i in 0..16 {
        state[i] = AES_SBOX[state[i] as usize];
    }
}

/// AES ShiftRows: cyclic left shift of rows.
fn aes_shift_rows(state: &mut Block) {
    // Row 0: no shift
    // Row 1: shift left by 1
    let t = state[1];
    state[1] = state[5]; state[5] = state[9]; state[9] = state[13]; state[13] = t;
    // Row 2: shift left by 2
    let t0 = state[2]; let t1 = state[6];
    state[2] = state[10]; state[6] = state[14]; state[10] = t0; state[14] = t1;
    // Row 3: shift left by 3 (= right by 1)
    let t = state[15];
    state[15] = state[11]; state[11] = state[7]; state[7] = state[3]; state[3] = t;
}

/// AES MixColumns: mix each column using GF(2^8) multiplication.
fn aes_mix_columns(state: &mut Block) {
    for col in 0..4 {
        let base = col * 4;
        let s0 = state[base];
        let s1 = state[base + 1];
        let s2 = state[base + 2];
        let s3 = state[base + 3];

        state[base]     = gf_mul2(s0) ^ gf_mul3(s1) ^ s2 ^ s3;
        state[base + 1] = s0 ^ gf_mul2(s1) ^ gf_mul3(s2) ^ s3;
        state[base + 2] = s0 ^ s1 ^ gf_mul2(s2) ^ gf_mul3(s3);
        state[base + 3] = gf_mul3(s0) ^ s1 ^ s2 ^ gf_mul2(s3);
    }
}

/// AES AddRoundKey: XOR state with round key.
fn aes_add_round_key(state: &mut Block, rk: &Block) {
    for i in 0..16 {
        state[i] ^= rk[i];
    }
}

/// AES-128 encrypt a single 16-byte block.
///
/// Performs 10 rounds: initial AddRoundKey, 9 full rounds, 1 final round
/// (no MixColumns).
pub fn aes128_encrypt(key: &AesKey, plaintext: &Block) -> Block {
    let rk = aes128_key_expansion(key);
    let mut state = *plaintext;

    // Initial round key addition
    aes_add_round_key(&mut state, &rk[0]);

    // Rounds 1-9: SubBytes + ShiftRows + MixColumns + AddRoundKey
    for round in 1..10 {
        aes_sub_bytes(&mut state);
        aes_shift_rows(&mut state);
        aes_mix_columns(&mut state);
        aes_add_round_key(&mut state, &rk[round]);
    }

    // Round 10: SubBytes + ShiftRows + AddRoundKey (no MixColumns)
    aes_sub_bytes(&mut state);
    aes_shift_rows(&mut state);
    aes_add_round_key(&mut state, &rk[10]);

    state
}

// =========================================================================
// CTR_DRBG (SP 800-90A Rev. 1, Section 10.2.1) — AES-128, no derivation function
// =========================================================================

/// CTR_DRBG internal state: Key and V (counter).
#[derive(Clone, Copy)]
pub struct CtrDrbgState {
    pub key: [u8; 16],
    pub v: [u8; 16],
}

/// Increment a 128-bit big-endian counter by 1, wrapping on overflow.
///
/// Treats the 16-byte array as a big-endian 128-bit integer and adds 1.
/// On overflow (0xFF...FF + 1), wraps to 0x00...00.
pub fn increment_counter(v: &[u8; 16]) -> [u8; 16] {
    let mut result = *v;
    let mut carry: u16 = 1;
    // Process from least significant byte (index 15) to most significant (index 0)
    for i in 0..16 {
        let idx = 15 - i;
        let sum = (result[idx] as u16) + carry;
        result[idx] = sum as u8;
        carry = sum >> 8;
    }
    result
}

/// CTR_DRBG Update function (SP 800-90A Rev. 1, Section 10.2.1.2).
///
/// Refreshes the DRBG state using provided_data (seedlen = 32 bytes).
/// For AES-128, seedlen = 32 bytes, so we need exactly 2 AES blocks.
///
/// Algorithm:
///   temp = empty
///   while len(temp) < seedlen:
///     V = (V + 1) mod 2^128
///     output_block = AES_Key(V)
///     temp = temp || output_block
///   temp = temp[0..seedlen]
///   temp = temp XOR provided_data
///   Key = temp[0..16]
///   V = temp[16..32]
///   return (Key, V)
pub fn ctr_drbg_update(state: CtrDrbgState, provided_data: [u8; SEEDLEN]) -> CtrDrbgState {
    let mut v = state.v;
    let mut temp = [0u8; SEEDLEN];

    // For AES-128, seedlen = 32 = 2 * blocklen, so we need exactly 2 blocks
    for i in 0..2 {
        v = increment_counter(&v);
        let output_block = aes128_encrypt(&state.key, &v);
        for j in 0..16 {
            temp[i * 16 + j] = output_block[j];
        }
    }

    // XOR with provided_data
    for i in 0..SEEDLEN {
        temp[i] ^= provided_data[i];
    }

    // Extract new Key and V
    let mut new_key = [0u8; 16];
    let mut new_v = [0u8; 16];
    for i in 0..16 {
        new_key[i] = temp[i];
        new_v[i] = temp[16 + i];
    }

    CtrDrbgState { key: new_key, v: new_v }
}

/// CTR_DRBG Instantiate function (SP 800-90A Rev. 1, Section 10.2.1.3).
///
/// Initializes a new DRBG state from entropy input and personalization string.
/// Both inputs are seedlen = 32 bytes. If personalization is shorter, it should
/// be zero-padded by the caller.
///
/// Algorithm:
///   Key = 0x00 * 16
///   V = 0x00 * 16
///   seed_material = entropy XOR personalization
///   (Key, V) = Update(seed_material, Key, V)
///   return (Key, V)
pub fn ctr_drbg_instantiate(entropy: [u8; SEEDLEN], personalization: [u8; SEEDLEN]) -> CtrDrbgState {
    let initial_state = CtrDrbgState {
        key: [0u8; 16],
        v: [0u8; 16],
    };

    // seed_material = entropy XOR personalization
    let mut seed_material = [0u8; SEEDLEN];
    for i in 0..SEEDLEN {
        seed_material[i] = entropy[i] ^ personalization[i];
    }

    ctr_drbg_update(initial_state, seed_material)
}

/// CTR_DRBG Generate function (SP 800-90A Rev. 1, Section 10.2.1.5).
///
/// Generates pseudorandom output blocks and updates the state.
/// `num_blocks` specifies how many 16-byte blocks to generate (capped at MAX_GEN_BLOCKS).
/// `additional_input` is optional additional data (32 bytes); the all-zero
/// array denotes a Null additional input.
///
/// Algorithm (Section 10.2.1.5.1):
///   If additional_input != Null:
///     (Key, V) = Update(additional_input, Key, V)
///   For i in 0..num_blocks:
///     V = (V + 1) mod 2^128
///     output_block\[i\] = AES_Key(V)
///   (Key, V) = Update(additional_input, Key, V)
///   return (output_blocks, (Key, V))
///
/// Returns (new_state, output_blocks).
pub fn ctr_drbg_generate(
    state: CtrDrbgState,
    num_blocks: usize,
    additional_input: [u8; SEEDLEN],
) -> (CtrDrbgState, [[u8; 16]; MAX_GEN_BLOCKS]) {
    // Step 2: with a non-Null additional input, refresh the state first.
    let mut has_additional_input = false;
    for i in 0..SEEDLEN {
        if additional_input[i] != 0 {
            has_additional_input = true;
        }
    }
    let state = if has_additional_input {
        ctr_drbg_update(state, additional_input)
    } else {
        state
    };

    let mut v = state.v;
    let mut output = [[0u8; 16]; MAX_GEN_BLOCKS];

    // Generate output blocks
    for i in 0..MAX_GEN_BLOCKS {
        if i >= num_blocks {
            break;
        }
        v = increment_counter(&v);
        output[i] = aes128_encrypt(&state.key, &v);
    }

    // Update state
    let gen_state = CtrDrbgState { key: state.key, v };
    let new_state = ctr_drbg_update(gen_state, additional_input);

    (new_state, output)
}

/// CTR_DRBG Reseed function (SP 800-90A Rev. 1, Section 10.2.1.4).
///
/// Reseeds the DRBG with new entropy and optional additional input.
///
/// Algorithm:
///   seed_material = entropy XOR additional_input
///   (Key, V) = Update(seed_material, Key, V)
///   return (Key, V)
pub fn ctr_drbg_reseed(
    state: CtrDrbgState,
    entropy: [u8; SEEDLEN],
    additional_input: [u8; SEEDLEN],
) -> CtrDrbgState {
    let mut seed_material = [0u8; SEEDLEN];
    for i in 0..SEEDLEN {
        seed_material[i] = entropy[i] ^ additional_input[i];
    }

    ctr_drbg_update(state, seed_material)
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    /// increment_counter is deterministic.
    #[kani::proof]
    fn increment_deterministic() {
        let v: [u8; 16] = kani::any();
        let r1 = increment_counter(&v);
        let r2 = increment_counter(&v);
        for i in 0..16 {
            assert_eq!(r1[i], r2[i]);
        }
    }

    /// XOR self is zero.
    #[kani::proof]
    fn xor_self_is_zero() {
        let a: [u8; 16] = kani::any();
        let result = xor_block(&a, &a);
        for i in 0..16 {
            assert_eq!(result[i], 0);
        }
    }

    /// XOR with zero is identity.
    #[kani::proof]
    fn xor_zero_identity() {
        let a: [u8; 16] = kani::any();
        let result = xor_block(&a, &ZERO_BLOCK);
        for i in 0..16 {
            assert_eq!(result[i], a[i]);
        }
    }
}

// =========================================================================
// Unit tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---- AES-128 sanity check (FIPS 197 Appendix B) ----

    #[test]
    fn test_aes128_fips197_appendix_b() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let pt: Block = [
            0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
            0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
        ];
        let expected_ct: Block = [
            0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb,
            0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
        ];
        let ct = aes128_encrypt(&key, &pt);
        assert_eq!(ct, expected_ct, "AES-128 FIPS 197 Appendix B");
    }

    // ---- increment_counter tests ----

    #[test]
    fn test_increment_counter_zero() {
        let v = [0u8; 16];
        let result = increment_counter(&v);
        let mut expected = [0u8; 16];
        expected[15] = 1;
        assert_eq!(result, expected, "increment 0 -> 1");
    }

    #[test]
    fn test_increment_counter_one() {
        let mut v = [0u8; 16];
        v[15] = 1;
        let result = increment_counter(&v);
        let mut expected = [0u8; 16];
        expected[15] = 2;
        assert_eq!(result, expected, "increment 1 -> 2");
    }

    #[test]
    fn test_increment_counter_0xff() {
        // 0x00...00FF + 1 = 0x00...0100
        let mut v = [0u8; 16];
        v[15] = 0xff;
        let result = increment_counter(&v);
        let mut expected = [0u8; 16];
        expected[14] = 0x01;
        assert_eq!(result, expected, "increment 0xFF -> 0x100");
    }

    #[test]
    fn test_increment_counter_carry_chain() {
        // 0x00...00FFFF + 1 = 0x00...010000
        let mut v = [0u8; 16];
        v[14] = 0xff;
        v[15] = 0xff;
        let result = increment_counter(&v);
        let mut expected = [0u8; 16];
        expected[13] = 0x01;
        assert_eq!(result, expected, "increment 0xFFFF -> 0x10000");
    }

    #[test]
    fn test_increment_counter_wrap() {
        // 0xFF...FF + 1 = 0x00...00 (wrap around)
        let v = [0xffu8; 16];
        let result = increment_counter(&v);
        assert_eq!(result, [0u8; 16], "increment 0xFF..FF wraps to 0");
    }

    #[test]
    fn test_increment_counter_mid_value() {
        // 0x00...0080 + 1 = 0x00...0081
        let mut v = [0u8; 16];
        v[15] = 0x80;
        let result = increment_counter(&v);
        let mut expected = [0u8; 16];
        expected[15] = 0x81;
        assert_eq!(result, expected, "increment 0x80 -> 0x81");
    }

    #[test]
    fn test_increment_counter_high_byte() {
        // Counter with high byte set: 0x01_00...00 + 1 = 0x01_00...01
        let mut v = [0u8; 16];
        v[0] = 0x01;
        let result = increment_counter(&v);
        let mut expected = [0u8; 16];
        expected[0] = 0x01;
        expected[15] = 0x01;
        assert_eq!(result, expected, "increment with high byte set");
    }

    // ---- Update tests ----

    #[test]
    fn test_update_with_zero_data() {
        let state = CtrDrbgState {
            key: [0u8; 16],
            v: [0u8; 16],
        };
        let zero_data = [0u8; SEEDLEN];
        let new_state = ctr_drbg_update(state, zero_data);

        // With Key=0, V=0:
        //   V1 = increment(0) = 0x00..01
        //   block1 = AES_{0}(0x00..01)
        //   V2 = increment(V1) = 0x00..02
        //   block2 = AES_{0}(0x00..02)
        //   temp = block1 || block2
        //   XOR with zeros -> temp unchanged
        //   new_key = block1, new_v = block2
        let v1 = increment_counter(&[0u8; 16]);
        let block1 = aes128_encrypt(&[0u8; 16], &v1);
        let v2 = increment_counter(&v1);
        let block2 = aes128_encrypt(&[0u8; 16], &v2);

        assert_eq!(new_state.key, block1, "Update zero: key = AES_0(0x01)");
        assert_eq!(new_state.v, block2, "Update zero: V = AES_0(0x02)");
    }

    #[test]
    fn test_update_deterministic() {
        let state = CtrDrbgState {
            key: [0x42u8; 16],
            v: [0x13u8; 16],
        };
        let data = [0xabu8; SEEDLEN];
        let s1 = ctr_drbg_update(state, data);
        let s2 = ctr_drbg_update(state, data);
        assert_eq!(s1.key, s2.key, "Update must be deterministic (key)");
        assert_eq!(s1.v, s2.v, "Update must be deterministic (V)");
    }

    // ---- Instantiate tests ----

    #[test]
    fn test_instantiate_zero_entropy_zero_perso() {
        let entropy = [0u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        // seed_material = 0 XOR 0 = 0
        // Update(0, Key=0, V=0) should give same as update_with_zero_data
        let expected = ctr_drbg_update(
            CtrDrbgState { key: [0u8; 16], v: [0u8; 16] },
            [0u8; SEEDLEN],
        );
        assert_eq!(state.key, expected.key, "Instantiate zero: key matches Update");
        assert_eq!(state.v, expected.v, "Instantiate zero: V matches Update");
    }

    #[test]
    fn test_instantiate_with_entropy() {
        let mut entropy = [0u8; SEEDLEN];
        for i in 0..SEEDLEN {
            entropy[i] = i as u8;
        }
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        // seed_material = entropy XOR 0 = entropy
        let expected = ctr_drbg_update(
            CtrDrbgState { key: [0u8; 16], v: [0u8; 16] },
            entropy,
        );
        assert_eq!(state.key, expected.key, "Instantiate with entropy: key");
        assert_eq!(state.v, expected.v, "Instantiate with entropy: V");
    }

    #[test]
    fn test_instantiate_entropy_xor_perso() {
        let entropy = [0xaau8; SEEDLEN];
        let perso = [0x55u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        // seed_material = 0xAA XOR 0x55 = 0xFF for each byte
        let expected = ctr_drbg_update(
            CtrDrbgState { key: [0u8; 16], v: [0u8; 16] },
            [0xffu8; SEEDLEN],
        );
        assert_eq!(state.key, expected.key, "Instantiate XOR: key");
        assert_eq!(state.v, expected.v, "Instantiate XOR: V");
    }

    // ---- Generate tests ----

    #[test]
    fn test_generate_one_block() {
        let mut entropy = [0u8; SEEDLEN];
        for i in 0..SEEDLEN {
            entropy[i] = (i as u8).wrapping_mul(7);
        }
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        let (new_state, output) = ctr_drbg_generate(state, 1, [0u8; SEEDLEN]);

        // Verify output is non-zero (extremely unlikely to be all zeros with real key)
        let is_nonzero = output[0].iter().any(|&b| b != 0);
        assert!(is_nonzero, "Generate should produce non-zero output");

        // Verify state changed
        assert_ne!(new_state.key, state.key, "Generate should change key");
        assert_ne!(new_state.v, state.v, "Generate should change V");
    }

    #[test]
    fn test_generate_multiple_blocks() {
        let entropy = [0x42u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        let (_new_state, output) = ctr_drbg_generate(state, 4, [0u8; SEEDLEN]);

        // All 4 blocks should be different (with overwhelming probability)
        for i in 0..4 {
            for j in (i + 1)..4 {
                assert_ne!(output[i], output[j],
                    "Generate blocks {} and {} should differ", i, j);
            }
        }

        // Blocks beyond num_blocks should be zero
        for i in 4..MAX_GEN_BLOCKS {
            assert_eq!(output[i], [0u8; 16],
                "Block {} beyond num_blocks should be zero", i);
        }
    }

    #[test]
    fn test_generate_deterministic() {
        let entropy = [0x37u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];

        let state1 = ctr_drbg_instantiate(entropy, perso);
        let state2 = ctr_drbg_instantiate(entropy, perso);

        let (ns1, out1) = ctr_drbg_generate(state1, 2, [0u8; SEEDLEN]);
        let (ns2, out2) = ctr_drbg_generate(state2, 2, [0u8; SEEDLEN]);

        assert_eq!(out1[0], out2[0], "First generation must be deterministic (block 0)");
        assert_eq!(out1[1], out2[1], "First generation must be deterministic (block 1)");
        assert_eq!(ns1.key, ns2.key, "State after generate must be deterministic (key)");
        assert_eq!(ns1.v, ns2.v, "State after generate must be deterministic (V)");
    }

    #[test]
    fn test_generate_twice_different_output() {
        let entropy = [0x99u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        let (state2, out1) = ctr_drbg_generate(state, 2, [0u8; SEEDLEN]);
        let (_state3, out2) = ctr_drbg_generate(state2, 2, [0u8; SEEDLEN]);

        // Second generation should produce different output
        assert_ne!(out1[0], out2[0],
            "Second generate call should produce different output (block 0)");
    }

    // ---- Reseed tests ----

    #[test]
    fn test_reseed_changes_state() {
        let entropy = [0x11u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        let new_entropy = [0x22u8; SEEDLEN];
        let reseeded = ctr_drbg_reseed(state, new_entropy, [0u8; SEEDLEN]);

        assert_ne!(reseeded.key, state.key, "Reseed should change key");
        assert_ne!(reseeded.v, state.v, "Reseed should change V");
    }

    #[test]
    fn test_reseed_then_generate() {
        let entropy = [0x33u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        let new_entropy = [0x44u8; SEEDLEN];
        let reseeded = ctr_drbg_reseed(state, new_entropy, [0u8; SEEDLEN]);

        let (_final_state, output) = ctr_drbg_generate(reseeded, 1, [0u8; SEEDLEN]);
        let is_nonzero = output[0].iter().any(|&b| b != 0);
        assert!(is_nonzero, "Generate after reseed should produce non-zero output");
    }

    #[test]
    fn test_reseed_deterministic() {
        let entropy = [0x55u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        let new_entropy = [0x66u8; SEEDLEN];
        let additional = [0x77u8; SEEDLEN];

        let r1 = ctr_drbg_reseed(state, new_entropy, additional);
        let r2 = ctr_drbg_reseed(state, new_entropy, additional);

        assert_eq!(r1.key, r2.key, "Reseed must be deterministic (key)");
        assert_eq!(r1.v, r2.v, "Reseed must be deterministic (V)");
    }

    // ---- Pin output test (regression) ----

    #[test]
    fn test_instantiate_generate_pinned() {
        // Pin the exact output so any code change is detected
        let entropy = [0u8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        // After instantiate with all zeros:
        // Initial: Key=0, V=0
        // Update(0, Key=0, V=0):
        //   V1 = 0x00..01, block1 = AES_0(V1)
        //   V2 = 0x00..02, block2 = AES_0(V2)
        //   new_key = block1, new_v = block2
        let v1 = increment_counter(&[0u8; 16]);
        let block1 = aes128_encrypt(&[0u8; 16], &v1);
        let v2 = increment_counter(&v1);
        let block2 = aes128_encrypt(&[0u8; 16], &v2);

        assert_eq!(state.key, block1, "Pinned: key after instantiate");
        assert_eq!(state.v, block2, "Pinned: V after instantiate");

        // Now generate 2 blocks
        let (new_state, output) = ctr_drbg_generate(state, 2, [0u8; SEEDLEN]);

        // Generate: V increments from state.v, encrypts under state.key
        let gen_v1 = increment_counter(&state.v);
        let gen_block1 = aes128_encrypt(&state.key, &gen_v1);
        let gen_v2 = increment_counter(&gen_v1);
        let gen_block2 = aes128_encrypt(&state.key, &gen_v2);

        assert_eq!(output[0], gen_block1, "Pinned: generate block 0");
        assert_eq!(output[1], gen_block2, "Pinned: generate block 1");

        // After generate, Update is called with V = gen_v2
        let post_gen_state = CtrDrbgState { key: state.key, v: gen_v2 };
        let expected_new = ctr_drbg_update(post_gen_state, [0u8; SEEDLEN]);
        assert_eq!(new_state.key, expected_new.key, "Pinned: key after generate");
        assert_eq!(new_state.v, expected_new.v, "Pinned: V after generate");
    }

    // ---- Reseed + Generate combined test ----

    #[test]
    fn test_reseed_generate_different_from_no_reseed() {
        let entropy = [0xaau8; SEEDLEN];
        let perso = [0u8; SEEDLEN];
        let state = ctr_drbg_instantiate(entropy, perso);

        // Path 1: generate directly
        let (_s1, out1) = ctr_drbg_generate(state, 2, [0u8; SEEDLEN]);

        // Path 2: reseed then generate
        let reseeded = ctr_drbg_reseed(state, [0xbbu8; SEEDLEN], [0u8; SEEDLEN]);
        let (_s2, out2) = ctr_drbg_generate(reseeded, 2, [0u8; SEEDLEN]);

        // Outputs must differ
        assert_ne!(out1[0], out2[0],
            "Reseed should cause different output (block 0)");
    }
}
