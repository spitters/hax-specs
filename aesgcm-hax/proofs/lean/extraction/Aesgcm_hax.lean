
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace Aesgcm_hax.Aes

--  Trait abstracting the AES-128 block cipher.
-- 
--  The AES round function involves S-box lookup tables which are complex
--  for hax extraction. This trait is axiomatized in the Lean bridge
--  (same pattern as SHAKE-128 in SLH-DSA).
class AesCipher.AssociatedTypes (Self : Type) where
  [trait_constr_AesCipher_i0 : Core_models.Marker.Copy.AssociatedTypes Self]

attribute [instance] AesCipher.AssociatedTypes.trait_constr_AesCipher_i0

class AesCipher (Self : Type)
  [associatedTypes : outParam (AesCipher.AssociatedTypes (Self : Type))]
  where
  [trait_constr_AesCipher_i0 : Core_models.Marker.Copy Self]
  aes128_encrypt_block (Self) :
    (Self -> (RustArray u8 16) -> (RustArray u8 16) -> RustM (RustArray u8 16))

attribute [instance] AesCipher.trait_constr_AesCipher_i0

end Aesgcm_hax.Aes


namespace Aesgcm_hax.Counter

--  XOR two 16-byte blocks.
def xor_blocks (a : (RustArray u8 16)) (b : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← ((← a[i]_?) ^^^? (← b[i]_?)))) :
        RustM (RustArray u8 16))));
  (pure out)

--  Construct J0 from a 96-bit nonce: J0 = nonce || 0x00000001.
-- 
--  Per NIST SP 800-38D Section 7.1, when the nonce is 96 bits,
--  the initial counter block is the nonce with a 32-bit counter
--  initialized to 1.
def make_j0 (nonce : (RustArray u8 12)) : RustM (RustArray u8 16) := do
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (12 : usize)
      (fun j0 _ => (do (pure true) : RustM Bool))
      j0
      (fun j0 i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          j0
          i
          (← nonce[i]_?)) :
        RustM (RustArray u8 16))));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (12 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (13 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (14 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (15 : usize)
      (1 : u8));
  (pure j0)

--  Increment the last 4 bytes of a block as a big-endian 32-bit counter.
-- 
--  Per NIST SP 800-38D Section 6.2, inc_32(X) increments the
--  rightmost 32 bits of X modulo 2^32, leaving the leftmost 96 bits
--  unchanged.
def inc32 (block : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← block[i]_?)) :
        RustM (RustArray u8 16))));
  let b15 : u16 ←
    ((← (Rust_primitives.Hax.cast_op (← out[(15 : usize)]_?))) +? (1 : u16));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (15 : usize)
      (← (Rust_primitives.Hax.cast_op (← (b15 &&&? (255 : u16))))));
  let carry : u16 ← (b15 >>>? (8 : i32));
  let b14 : u16 ←
    ((← (Rust_primitives.Hax.cast_op (← out[(14 : usize)]_?))) +? carry);
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (14 : usize)
      (← (Rust_primitives.Hax.cast_op (← (b14 &&&? (255 : u16))))));
  let carry : u16 ← (b14 >>>? (8 : i32));
  let b13 : u16 ←
    ((← (Rust_primitives.Hax.cast_op (← out[(13 : usize)]_?))) +? carry);
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (13 : usize)
      (← (Rust_primitives.Hax.cast_op (← (b13 &&&? (255 : u16))))));
  let carry : u16 ← (b13 >>>? (8 : i32));
  let b12 : u16 ←
    ((← (Rust_primitives.Hax.cast_op (← out[(12 : usize)]_?))) +? carry);
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (12 : usize)
      (← (Rust_primitives.Hax.cast_op (← (b12 &&&? (255 : u16))))));
  (pure out)

--  Encrypt one block in counter (GCTR) mode.
-- 
--  GCTR_K(counter, input) = input XOR AES_K(counter).
def gctr_one_block
    (C : Type)
    [trait_constr_gctr_one_block_associated_type_i0 :
      Aesgcm_hax.Aes.AesCipher.AssociatedTypes
      C]
    [trait_constr_gctr_one_block_i0 : Aesgcm_hax.Aes.AesCipher C ]
    (crypto : C)
    (key : (RustArray u8 16))
    (counter : (RustArray u8 16))
    (input : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let encrypted_counter : (RustArray u8 16) ←
    (Aesgcm_hax.Aes.AesCipher.aes128_encrypt_block C crypto key counter);
  (xor_blocks input encrypted_counter)

end Aesgcm_hax.Counter


namespace Aesgcm_hax.Gcm

--  Trait abstracting GCM cryptographic primitives.
-- 
--  Extends `AesCipher` with GHASH multiplication in GF(2^128).
--  The finite field multiplication is complex for hax extraction,
--  so it is abstracted via this trait and axiomatized in the Lean bridge.
class GcmCrypto.AssociatedTypes (Self : Type) where
  [trait_constr_GcmCrypto_i0 : Core_models.Marker.Copy.AssociatedTypes Self]
  [trait_constr_GcmCrypto_i1 : Aesgcm_hax.Aes.AesCipher.AssociatedTypes Self]

attribute [instance] GcmCrypto.AssociatedTypes.trait_constr_GcmCrypto_i0

attribute [instance] GcmCrypto.AssociatedTypes.trait_constr_GcmCrypto_i1

class GcmCrypto (Self : Type)
  [associatedTypes : outParam (GcmCrypto.AssociatedTypes (Self : Type))]
  where
  [trait_constr_GcmCrypto_i0 : Core_models.Marker.Copy Self]
  [trait_constr_GcmCrypto_i1 : Aesgcm_hax.Aes.AesCipher Self]
  ghash_multiply (Self) :
    (Self -> (RustArray u8 16) -> (RustArray u8 16) -> RustM (RustArray u8 16))

attribute [instance] GcmCrypto.trait_constr_GcmCrypto_i0

attribute [instance] GcmCrypto.trait_constr_GcmCrypto_i1

--  Zero block constant.
def zero_block (_ : Rust_primitives.Hax.Tuple0) : RustM (RustArray u8 16) := do
  (Rust_primitives.Hax.repeat (0 : u8) (16 : usize))

--  Encode a u64 as 8 big-endian bytes into a buffer starting at `offset`.
def encode_u64_be (buf : (RustArray u8 16)) (offset : usize) (value : u64) :
    RustM (RustArray u8 16) := do
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      offset
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (56 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (1 : usize)))
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (48 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (2 : usize)))
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (40 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (3 : usize)))
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (32 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (4 : usize)))
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (24 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (5 : usize)))
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (16 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (6 : usize)))
      (← (Rust_primitives.Hax.cast_op
        (← ((← (value >>>? (8 : i32))) &&&? (255 : u64))))));
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      buf
      (← (offset +? (7 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (value &&&? (255 : u64))))));
  (pure buf)

--  Build the length block for GHASH: [len(A) in bits || len(C) in bits].
-- 
--  Per NIST SP 800-38D Section 6.4, the final GHASH input is the
--  concatenation of the bit lengths of AAD and ciphertext, each
--  encoded as a 64-bit big-endian integer.
def make_len_block (aad_bytes : u64) (ct_bytes : u64) :
    RustM (RustArray u8 16) := do
  let block : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let aad_bits : u64 ← (aad_bytes *? (8 : u64));
  let ct_bits : u64 ← (ct_bytes *? (8 : u64));
  let block : (RustArray u8 16) ← (encode_u64_be block (0 : usize) aad_bits);
  let block : (RustArray u8 16) ← (encode_u64_be block (8 : usize) ct_bits);
  (pure block)

--  Extract a 16-byte block from a 64-byte array at the given block index.
def extract_block (data : (RustArray u8 64)) (block_idx : usize) :
    RustM (RustArray u8 16) := do
  let block : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let offset : usize ← (block_idx *? (16 : usize));
  let block : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun block _ => (do (pure true) : RustM Bool))
      block
      (fun block i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          block
          i
          (← data[(← (offset +? i))]_?)) :
        RustM (RustArray u8 16))));
  (pure block)

--  Write a 16-byte block into a 64-byte array at the given block index.
def write_block
    (data : (RustArray u8 64))
    (block_idx : usize)
    (block : (RustArray u8 16)) :
    RustM (RustArray u8 64) := do
  let offset : usize ← (block_idx *? (16 : usize));
  let data : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun data _ => (do (pure true) : RustM Bool))
      data
      (fun data i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          data
          (← (offset +? i))
          (← block[i]_?)) :
        RustM (RustArray u8 64))));
  (pure data)

--  Perform one GHASH step: state = (state XOR block) * H.
def ghash_step
    (C : Type)
    [trait_constr_ghash_step_associated_type_i0 : GcmCrypto.AssociatedTypes C]
    [trait_constr_ghash_step_i0 : GcmCrypto C ]
    (crypto : C)
    (h : (RustArray u8 16))
    (state : (RustArray u8 16))
    (block : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let xored : (RustArray u8 16) ← (Aesgcm_hax.Counter.xor_blocks state block);
  (GcmCrypto.ghash_multiply C crypto h xored)

--  Compute GHASH over AAD (1 block), ciphertext (4 blocks), and length block.
-- 
--  GHASH_H(A, C) processes:
--    1. AAD block
--    2. Ciphertext blocks (4 blocks = 64 bytes)
--    3. Length block [len(A) || len(C)] in bits
def ghash_compute
    (C : Type)
    [trait_constr_ghash_compute_associated_type_i0 : GcmCrypto.AssociatedTypes
      C]
    [trait_constr_ghash_compute_i0 : GcmCrypto C ]
    (crypto : C)
    (h : (RustArray u8 16))
    (aad : (RustArray u8 16))
    (ciphertext : (RustArray u8 64)) :
    RustM (RustArray u8 16) := do
  let zero : (RustArray u8 16) ← (zero_block Rust_primitives.Hax.Tuple0.mk);
  let state : (RustArray u8 16) ← (ghash_step C crypto h zero aad);
  let ct_block_0 : (RustArray u8 16) ← (extract_block ciphertext (0 : usize));
  let state : (RustArray u8 16) ← (ghash_step C crypto h state ct_block_0);
  let ct_block_1 : (RustArray u8 16) ← (extract_block ciphertext (1 : usize));
  let state : (RustArray u8 16) ← (ghash_step C crypto h state ct_block_1);
  let ct_block_2 : (RustArray u8 16) ← (extract_block ciphertext (2 : usize));
  let state : (RustArray u8 16) ← (ghash_step C crypto h state ct_block_2);
  let ct_block_3 : (RustArray u8 16) ← (extract_block ciphertext (3 : usize));
  let state : (RustArray u8 16) ← (ghash_step C crypto h state ct_block_3);
  let len_block : (RustArray u8 16) ← (make_len_block (16 : u64) (64 : u64));
  let state : (RustArray u8 16) ← (ghash_step C crypto h state len_block);
  (pure state)

--  Encrypt 4 blocks (64 bytes) using AES-128-GCM.
-- 
--  Implements NIST SP 800-38D Section 7.1 (GCM-AE_K):
--    1. H = AES_K(0^128)
--    2. J0 = nonce || 0x00000001
--    3. For i in 0..3: C_i = P_i XOR AES_K(inc32^{i+1}(J0))
--    4. T = GHASH_H(A, C) XOR AES_K(J0)
-- 
--  # Arguments
--  * `crypto` - Cryptographic primitives (AES + GHASH)
--  * `key` - AES-128 key
--  * `nonce` - 96-bit nonce
--  * `aad` - Additional authenticated data (one 16-byte block)
--  * `plaintext` - 64 bytes of plaintext (4 AES blocks)
-- 
--  # Returns
--  Tuple of (ciphertext, authentication tag).
def gcm_encrypt
    (C : Type)
    [trait_constr_gcm_encrypt_associated_type_i0 : GcmCrypto.AssociatedTypes C]
    [trait_constr_gcm_encrypt_i0 : GcmCrypto C ]
    (crypto : C)
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (aad : (RustArray u8 16))
    (plaintext : (RustArray u8 64)) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 64) (RustArray u8 16)) := do
  let zero : (RustArray u8 16) ← (zero_block Rust_primitives.Hax.Tuple0.mk);
  let h : (RustArray u8 16) ←
    (Aesgcm_hax.Aes.AesCipher.aes128_encrypt_block C crypto key zero);
  let j0 : (RustArray u8 16) ← (Aesgcm_hax.Counter.make_j0 nonce);
  let ciphertext : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 j0);
  let pt_block_0 : (RustArray u8 16) ← (extract_block plaintext (0 : usize));
  let ct_block_0 : (RustArray u8 16) ←
    (Aesgcm_hax.Counter.gctr_one_block C crypto key counter pt_block_0);
  let ciphertext : (RustArray u8 64) ←
    (write_block ciphertext (0 : usize) ct_block_0);
  let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 counter);
  let pt_block_1 : (RustArray u8 16) ← (extract_block plaintext (1 : usize));
  let ct_block_1 : (RustArray u8 16) ←
    (Aesgcm_hax.Counter.gctr_one_block C crypto key counter pt_block_1);
  let ciphertext : (RustArray u8 64) ←
    (write_block ciphertext (1 : usize) ct_block_1);
  let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 counter);
  let pt_block_2 : (RustArray u8 16) ← (extract_block plaintext (2 : usize));
  let ct_block_2 : (RustArray u8 16) ←
    (Aesgcm_hax.Counter.gctr_one_block C crypto key counter pt_block_2);
  let ciphertext : (RustArray u8 64) ←
    (write_block ciphertext (2 : usize) ct_block_2);
  let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 counter);
  let pt_block_3 : (RustArray u8 16) ← (extract_block plaintext (3 : usize));
  let ct_block_3 : (RustArray u8 16) ←
    (Aesgcm_hax.Counter.gctr_one_block C crypto key counter pt_block_3);
  let ciphertext : (RustArray u8 64) ←
    (write_block ciphertext (3 : usize) ct_block_3);
  let ghash_result : (RustArray u8 16) ←
    (ghash_compute C crypto h aad ciphertext);
  let tag : (RustArray u8 16) ←
    (Aesgcm_hax.Counter.gctr_one_block C crypto key j0 ghash_result);
  (pure (Rust_primitives.Hax.Tuple2.mk ciphertext tag))

--  Compare two 16-byte tags in constant time.
-- 
--  Returns `true` if and only if all bytes are equal.
def tags_equal (a : (RustArray u8 16)) (b : (RustArray u8 16)) :
    RustM Bool := do
  let acc : u8 := (0 : u8);
  let acc : u8 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun acc _ => (do (pure true) : RustM Bool))
      acc
      (fun acc i =>
        (do
        (Rust_primitives.Hax.Machine_int.bitor
          acc
          (← ((← a[i]_?) ^^^? (← b[i]_?)))) :
        RustM u8)));
  (Rust_primitives.Hax.Machine_int.eq acc (0 : u8))

--  Decrypt 4 blocks (64 bytes) using AES-128-GCM.
-- 
--  Implements NIST SP 800-38D Section 7.2 (GCM-AD_K):
--    1. H = AES_K(0^128)
--    2. J0 = nonce || 0x00000001
--    3. Recompute tag from AAD and ciphertext
--    4. Verify tag; if mismatch return None
--    5. For i in 0..3: P_i = C_i XOR AES_K(inc32^{i+1}(J0))
-- 
--  # Arguments
--  * `crypto` - Cryptographic primitives (AES + GHASH)
--  * `key` - AES-128 key
--  * `nonce` - 96-bit nonce
--  * `aad` - Additional authenticated data (one 16-byte block)
--  * `ciphertext` - 64 bytes of ciphertext (4 AES blocks)
--  * `tag` - Authentication tag to verify
-- 
--  # Returns
--  `Some(plaintext)` if tag verification succeeds, `None` otherwise.
def gcm_decrypt
    (C : Type)
    [trait_constr_gcm_decrypt_associated_type_i0 : GcmCrypto.AssociatedTypes C]
    [trait_constr_gcm_decrypt_i0 : GcmCrypto C ]
    (crypto : C)
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (aad : (RustArray u8 16))
    (ciphertext : (RustArray u8 64))
    (tag : (RustArray u8 16)) :
    RustM (Core_models.Option.Option (RustArray u8 64)) := do
  let zero : (RustArray u8 16) ← (zero_block Rust_primitives.Hax.Tuple0.mk);
  let h : (RustArray u8 16) ←
    (Aesgcm_hax.Aes.AesCipher.aes128_encrypt_block C crypto key zero);
  let j0 : (RustArray u8 16) ← (Aesgcm_hax.Counter.make_j0 nonce);
  let ghash_result : (RustArray u8 16) ←
    (ghash_compute C crypto h aad ciphertext);
  let expected_tag : (RustArray u8 16) ←
    (Aesgcm_hax.Counter.gctr_one_block C crypto key j0 ghash_result);
  if (← (Core_models.Ops.Bit.Not.not (← (tags_equal tag expected_tag)))) then
    (pure Core_models.Option.Option.None)
  else
    let plaintext : (RustArray u8 64) ←
      (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
    let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 j0);
    let ct_block_0 : (RustArray u8 16) ← (extract_block ciphertext (0 : usize));
    let pt_block_0 : (RustArray u8 16) ←
      (Aesgcm_hax.Counter.gctr_one_block C crypto key counter ct_block_0);
    let plaintext : (RustArray u8 64) ←
      (write_block plaintext (0 : usize) pt_block_0);
    let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 counter);
    let ct_block_1 : (RustArray u8 16) ← (extract_block ciphertext (1 : usize));
    let pt_block_1 : (RustArray u8 16) ←
      (Aesgcm_hax.Counter.gctr_one_block C crypto key counter ct_block_1);
    let plaintext : (RustArray u8 64) ←
      (write_block plaintext (1 : usize) pt_block_1);
    let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 counter);
    let ct_block_2 : (RustArray u8 16) ← (extract_block ciphertext (2 : usize));
    let pt_block_2 : (RustArray u8 16) ←
      (Aesgcm_hax.Counter.gctr_one_block C crypto key counter ct_block_2);
    let plaintext : (RustArray u8 64) ←
      (write_block plaintext (2 : usize) pt_block_2);
    let counter : (RustArray u8 16) ← (Aesgcm_hax.Counter.inc32 counter);
    let ct_block_3 : (RustArray u8 16) ← (extract_block ciphertext (3 : usize));
    let pt_block_3 : (RustArray u8 16) ←
      (Aesgcm_hax.Counter.gctr_one_block C crypto key counter ct_block_3);
    let plaintext : (RustArray u8 64) ←
      (write_block plaintext (3 : usize) pt_block_3);
    (pure (Core_models.Option.Option.Some plaintext))

end Aesgcm_hax.Gcm


namespace Aesgcm_hax.Types

--  AES-128 key (128 bits).
abbrev AesKey : Type := (RustArray u8 16)

--  AES block (128 bits).
abbrev AesBlock : Type := (RustArray u8 16)

--  GCM nonce (96 bits).
abbrev GcmNonce : Type := (RustArray u8 12)

--  GCM authentication tag (128 bits).
abbrev GcmTag : Type := (RustArray u8 16)

--  GHASH accumulator state (128 bits).
abbrev GcmState : Type := (RustArray u8 16)

end Aesgcm_hax.Types

