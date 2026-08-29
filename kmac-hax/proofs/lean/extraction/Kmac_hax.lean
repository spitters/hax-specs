
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


namespace Kmac_hax

--  Result of left_encode or right_encode: up to 9 bytes (1 byte count + 8 value bytes).
--  `len` is the number of valid bytes in `data`.
structure Encoded9 where
  data : (RustArray u8 9)
  len : usize

@[instance] opaque Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes Encoded9 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  Core_models.Clone.Clone Encoded9 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes Encoded9 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Marker.Copy Encoded9 :=
  by constructor <;> exact Inhabited.default

--  Result of encode_string: up to 9 + KEY_MAX bytes.
--  We use 41 = 9 (left_encode) + 32 (max key bytes for KMAC-256).
--  `len` is the number of valid bytes in `data`.
structure Encoded41 where
  data : (RustArray u8 41)
  len : usize

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes Encoded41 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Clone.Clone Encoded41 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes Encoded41 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  Core_models.Marker.Copy Encoded41 :=
  by constructor <;> exact Inhabited.default

--  Count the number of bytes needed to represent `x` in big-endian.
--  Returns 1 for x == 0 (the spec encodes 0 as a single zero byte).
--  Uses a bounded for-loop instead of while for hax compatibility.
def byte_count (x : usize) : RustM u8 := do
  if (← (Rust_primitives.Hax.Machine_int.eq x (0 : usize))) then
    (pure (1 : u8))
  else
    let n : u8 := (0 : u8);
    (Rust_primitives.Hax.Folds.fold_range
      (0 : u8)
      (8 : u8)
      (fun n _ => (do (pure true) : RustM Bool))
      n
      (fun n i =>
        (do
        let shift : u32 ←
          (Core_models.Num.Impl_8.wrapping_mul
            (← (Rust_primitives.Hax.cast_op i))
            (8 : u32));
        if (← (Rust_primitives.Hax.Machine_int.lt shift (64 : u32))) then
          let shifted : usize ←
            (x >>>? (← (Rust_primitives.Hax.cast_op shift)));
          if (← (Rust_primitives.Hax.Machine_int.gt shifted (0 : usize))) then
            let n : u8 ← (Core_models.Num.Impl_6.wrapping_add i (1 : u8));
            (pure n)
          else
            (pure n)
        else
          (pure n) :
        RustM u8)))

--  Left-encode an integer x.
-- 
--  Encoding: `n || x_1 || x_2 || ... || x_n`
--  where n is the number of bytes needed to represent x (big-endian).
-- 
def left_encode (x : usize) : RustM Encoded9 := do
  let out : (RustArray u8 9) ←
    (Rust_primitives.Hax.repeat (0 : u8) (9 : usize));
  let n : u8 ← (byte_count x);
  let out : (RustArray u8 9) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      n);
  let out : (RustArray u8 9) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : u8)
      (8 : u8)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i n)) then
          let out_idx : usize ←
            (Rust_primitives.Hax.cast_op
              (← (Core_models.Num.Impl_6.wrapping_sub n i)));
          let shift : u32 ←
            (Core_models.Num.Impl_8.wrapping_mul
              (← (Rust_primitives.Hax.cast_op i))
              (8 : u32));
          let byte_val : u8 ←
            if (← (Rust_primitives.Hax.Machine_int.lt shift (64 : u32))) then
              (Rust_primitives.Hax.cast_op
                (← ((← (x >>>? (← (Rust_primitives.Hax.cast_op shift))))
                  &&&? (255 : usize))))
            else
              (pure (0 : u8));
          let out : (RustArray u8 9) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              out_idx
              byte_val);
          (pure out)
        else
          (pure out) :
        RustM (RustArray u8 9))));
  (pure (Encoded9.mk
    (data := out)
    (len := (← (Core_models.Num.Impl_11.wrapping_add
      (← (Rust_primitives.Hax.cast_op n))
      (1 : usize))))))

--  Right-encode an integer x.
-- 
--  Encoding: `x_1 || x_2 || ... || x_n || n`
--  where n is the number of bytes needed to represent x (big-endian).
-- 
def right_encode (x : usize) : RustM Encoded9 := do
  let out : (RustArray u8 9) ←
    (Rust_primitives.Hax.repeat (0 : u8) (9 : usize));
  let n : u8 ← (byte_count x);
  let out : (RustArray u8 9) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : u8)
      (8 : u8)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i n)) then
          let out_idx : usize ←
            (Rust_primitives.Hax.cast_op
              (← (Core_models.Num.Impl_6.wrapping_sub
                (← (Core_models.Num.Impl_6.wrapping_sub n (1 : u8)))
                i)));
          let shift : u32 ←
            (Core_models.Num.Impl_8.wrapping_mul
              (← (Rust_primitives.Hax.cast_op i))
              (8 : u32));
          let byte_val : u8 ←
            if (← (Rust_primitives.Hax.Machine_int.lt shift (64 : u32))) then
              (Rust_primitives.Hax.cast_op
                (← ((← (x >>>? (← (Rust_primitives.Hax.cast_op shift))))
                  &&&? (255 : usize))))
            else
              (pure (0 : u8));
          let out : (RustArray u8 9) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              out_idx
              byte_val);
          (pure out)
        else
          (pure out) :
        RustM (RustArray u8 9))));
  let out : (RustArray u8 9) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (← (Rust_primitives.Hax.cast_op n))
      n);
  (pure (Encoded9.mk
    (data := out)
    (len := (← (Core_models.Num.Impl_11.wrapping_add
      (← (Rust_primitives.Hax.cast_op n))
      (1 : usize))))))

--  Encode a byte string of up to 32 bytes.
-- 
--  `encode_string(S) = left_encode(len(S) * 8) || S`
-- 
--  The length argument is in bits (hence * 8).
--  Buffer is 41 bytes: up to 9 for left_encode + up to 32 for the string.
-- 
def encode_string_32 (s : (RustArray u8 32)) (s_len : usize) :
    RustM Encoded41 := do
  let out : (RustArray u8 41) ←
    (Rust_primitives.Hax.repeat (0 : u8) (41 : usize));
  let bit_len : usize ←
    (Core_models.Num.Impl_11.wrapping_mul s_len (8 : usize));
  let le : Encoded9 ← (left_encode bit_len);
  let out : (RustArray u8 41) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (9 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i (Encoded9.len le))) then
          let out : (RustArray u8 41) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              i
              (← (Encoded9.data le)[i]_?));
          (pure out)
        else
          (pure out) :
        RustM (RustArray u8 41))));
  let offset : usize := (Encoded9.len le);
  let out : (RustArray u8 41) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (32 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out j =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt j s_len)) then
          let dst : usize ← (Core_models.Num.Impl_11.wrapping_add offset j);
          if (← (Rust_primitives.Hax.Machine_int.lt dst (41 : usize))) then
            let out : (RustArray u8 41) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                out
                dst
                (← s[j]_?));
            (pure out)
          else
            (pure out)
        else
          (pure out) :
        RustM (RustArray u8 41))));
  (pure (Encoded41.mk
    (data := out)
    (len := (← (Core_models.Num.Impl_11.wrapping_add offset s_len)))))

--  Bytepad X to a w-byte boundary.
-- 
--  `bytepad(X, w) = left_encode(w) || X || 0*`
--  where `0*` pads to the next multiple of `w` bytes.
-- 
--  Returns a 168-byte buffer (KMAC-128 rate). For KMAC-256 (rate 136),
--  only the first 136 bytes are meaningful.
-- 
def bytepad (x_data : (RustArray u8 41)) (x_len : usize) (w : usize) :
    RustM (RustArray u8 168) := do
  let out : (RustArray u8 168) ←
    (Rust_primitives.Hax.repeat (0 : u8) (168 : usize));
  let le_w : Encoded9 ← (left_encode w);
  let out : (RustArray u8 168) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (9 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i (Encoded9.len le_w))) then
          let out : (RustArray u8 168) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              i
              (← (Encoded9.data le_w)[i]_?));
          (pure out)
        else
          (pure out) :
        RustM (RustArray u8 168))));
  let offset : usize := (Encoded9.len le_w);
  let out : (RustArray u8 168) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (41 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out j =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt j x_len)) then
          let dst : usize ← (Core_models.Num.Impl_11.wrapping_add offset j);
          if (← (Rust_primitives.Hax.Machine_int.lt dst (168 : usize))) then
            let out : (RustArray u8 168) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                out
                dst
                (← x_data[j]_?));
            (pure out)
          else
            (pure out)
        else
          (pure out) :
        RustM (RustArray u8 168))));
  (pure out)

--  Assemble the cSHAKE-128 input for KMAC-128.
-- 
--  KMAC128(K, X, L, S) =
--    cSHAKE128(bytepad(encode_string(K), 168) || X || right_encode(L),
--              L, "KMAC", S)
-- 
--  This function constructs the pre-image bytes that feed into cSHAKE-128.
--  The actual sponge evaluation is abstracted (requires Keccak).
-- 
--  Parameters:
--  - `key`: 32-byte KMAC key (256-bit)
--  - `data`: 64-byte input message
--  - `out_bits`: desired output length in bits (e.g. 256)
-- 
--  Returns a 241-byte buffer containing:
--    bytepad(encode_string(K), 168) || data || right_encode(out_bits)
--  and the number of valid bytes.
-- 
structure KmacPreimage where
  padded_key : (RustArray u8 168)
  data : (RustArray u8 64)
  right_enc_l : Encoded9

@[instance] opaque Impl_4.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes KmacPreimage :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  Core_models.Clone.Clone KmacPreimage :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes KmacPreimage :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  Core_models.Marker.Copy KmacPreimage :=
  by constructor <;> exact Inhabited.default

def kmac128_preimage
    (key : (RustArray u8 32))
    (data : (RustArray u8 64))
    (out_bits : usize) :
    RustM KmacPreimage := do
  let encoded_key : Encoded41 ← (encode_string_32 key (32 : usize));
  let padded_key : (RustArray u8 168) ←
    (bytepad
      (Encoded41.data encoded_key)
      (Encoded41.len encoded_key)
      (168 : usize));
  let re_l : Encoded9 ← (right_encode out_bits);
  (pure (KmacPreimage.mk
    (padded_key := padded_key)
    (data := data)
    (right_enc_l := re_l)))

--  Assemble the cSHAKE-256 input for KMAC-256.
-- 
--  Same as KMAC-128 but uses cSHAKE-256 (rate 136) instead of
--  cSHAKE-128 (rate 168).
-- 
def kmac256_preimage
    (key : (RustArray u8 32))
    (data : (RustArray u8 64))
    (out_bits : usize) :
    RustM KmacPreimage := do
  let encoded_key : Encoded41 ← (encode_string_32 key (32 : usize));
  let padded_key : (RustArray u8 168) ←
    (bytepad
      (Encoded41.data encoded_key)
      (Encoded41.len encoded_key)
      (136 : usize));
  let re_l : Encoded9 ← (right_encode out_bits);
  (pure (KmacPreimage.mk
    (padded_key := padded_key)
    (data := data)
    (right_enc_l := re_l)))

end Kmac_hax

