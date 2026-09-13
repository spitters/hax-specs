
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


namespace Plonky3_hax.Specs.Baby_bear

--  The Baby Bear prime: p = 2^31 - 2^27 + 1.
def BABY_BEAR_PRIME : u64 := (2013265921 : u64)

--  Additive identity.
def ZERO : u64 := (0 : u64)

--  Multiplicative identity.
def ONE : u64 := (1 : u64)

--  A generator of the multiplicative group F_p^* (`MONTY_GEN` in `p3-baby-bear`).
-- 
--  The 2^k-th roots of unity are `bb_pow(GENERATOR, (p-1) / 2^k)`.
def GENERATOR : u64 := (31 : u64)

--  Reduce `x` to `[0, p)` by one conditional subtraction.
-- 
--  Requires `x < 2p`.
def bb_reduce (x : u64) : RustM u64 := do
  if (← (Rust_primitives.Hax.Machine_int.ge x BABY_BEAR_PRIME)) then
    (x -? BABY_BEAR_PRIME)
  else
    (pure x)

--  Add two Baby Bear field elements: (a + b) mod p.
-- 
--  For canonical `a` and `b` the sum is below `2p`, so one conditional
--  subtraction reduces it.
def bb_add (a : u64) (b : u64) : RustM u64 := do (bb_reduce (← (a +? b)))

--  Subtract two Baby Bear field elements: (a - b) mod p.
-- 
--  If `a < b`, the result is `a + p - b`.
def bb_sub (a : u64) (b : u64) : RustM u64 := do
  if (← (Rust_primitives.Hax.Machine_int.ge a b)) then
    (a -? b)
  else
    ((← (a +? BABY_BEAR_PRIME)) -? b)

--  Negate a Baby Bear field element: `(-a) mod p`, which is `p - a` for
--  `a != 0` and `0` for `a = 0`.
def bb_neg (a : u64) : RustM u64 := do
  if (← (Rust_primitives.Hax.Machine_int.eq a (0 : u64))) then
    (pure (0 : u64))
  else
    (BABY_BEAR_PRIME -? a)

--  Multiply two Baby Bear field elements: (a * b) mod p.
-- 
--  The product is formed in `u128` and reduced with `%`. For canonical
--  inputs it is below 2^62, so the widening only removes the overflow case
--  for non-canonical inputs.
def bb_mul (a : u64) (b : u64) : RustM u64 := do
  let product : u128 ←
    ((← (Rust_primitives.Hax.cast_op a))
      *? (← (Rust_primitives.Hax.cast_op b)));
  (Rust_primitives.Hax.cast_op
    (← (product %? (← (Rust_primitives.Hax.cast_op BABY_BEAR_PRIME)))))

--  Square a Baby Bear field element: a^2 mod p.
def bb_square (a : u64) : RustM u64 := do (bb_mul a a)

--  Compute `base^exp mod p` by right-to-left square-and-multiply.
-- 
--  `exp` is any `u64`; the loop runs at most 64 iterations, one per exponent
--  bit, and `bb_pow(base, 0) = 1` for every `base`, including `0`.
def bb_pow (base : u64) (exp : u64) : RustM u64 := do
  if (← (Rust_primitives.Hax.Machine_int.eq exp (0 : u64))) then
    (pure ONE)
  else
    let result : u64 := ONE;
    let cur_base : u64 := base;
    let e : u64 := exp;
    let ⟨cur_base, e, result⟩ ←
      (Rust_primitives.Hax.Folds.fold_range_cf
        (0 : i32)
        (64 : i32)
        (fun ⟨cur_base, e, result⟩ _ => (do (pure true) : RustM Bool))
        (Rust_primitives.Hax.Tuple3.mk cur_base e result)
        (fun ⟨cur_base, e, result⟩ _ =>
          (do
          let result : u64 ←
            if
            (← (Rust_primitives.Hax.Machine_int.eq
              (← (e &&&? (1 : u64)))
              (1 : u64))) then
              let result : u64 ← (bb_mul result cur_base);
              (pure result)
            else
              (pure result);
          let cur_base : u64 ← (bb_square cur_base);
          let e : u64 ← (e >>>? (1 : i32));
          if (← (Rust_primitives.Hax.Machine_int.eq e (0 : u64))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Rust_primitives.Hax.Tuple2.mk
                Rust_primitives.Hax.Tuple0.mk
                (Rust_primitives.Hax.Tuple3.mk cur_base e result))))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (Rust_primitives.Hax.Tuple3.mk cur_base e result))) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Rust_primitives.Hax.Tuple2
              Rust_primitives.Hax.Tuple0
              (Rust_primitives.Hax.Tuple3 u64 u64 u64))
            (Rust_primitives.Hax.Tuple3 u64 u64 u64)))));
    (pure result)

--  Compute the multiplicative inverse of a: a^{-1} mod p.
-- 
--  Computed as `a^(p-2)` (Fermat's little theorem). Returns `0` for `a = 0`.
def bb_inv (a : u64) : RustM u64 := do
  if (← (Rust_primitives.Hax.Machine_int.eq a (0 : u64))) then
    (pure ZERO)
  else
    (bb_pow a (← (BABY_BEAR_PRIME -? (2 : u64))))

--  Division: `a * bb_inv(b)`, hence `bb_div(a, 0) = 0`.
def bb_div (a : u64) (b : u64) : RustM u64 := do (bb_mul a (← (bb_inv b)))

--  Compute a primitive 2^k-th root of unity in the Baby Bear field.
-- 
--  Returns `GENERATOR^((p-1) / 2^k)`, which has multiplicative order exactly
--  `2^k`. Requires `k <= 27`; the values for `k = 0..=27` equal
--  `TWO_ADIC_GENERATORS[k]` of `p3-baby-bear` 0.5.
def bb_root_of_unity (k : u32) : RustM u64 := do
  let p_minus_one : u64 ← (BABY_BEAR_PRIME -? (1 : u64));
  let exponent : u64 ← (p_minus_one >>>? k);
  (bb_pow GENERATOR exponent)

--  Evaluate a polynomial at a point using Horner's method.
-- 
--  `coeffs[i]` is the coefficient of `x^i`; the empty polynomial evaluates
--  to `0`.
def bb_poly_eval (coeffs : (RustSlice u64)) (point : u64) : RustM u64 := do
  let len : usize ← (Core_models.Slice.Impl.len u64 coeffs);
  if (← (Rust_primitives.Hax.Machine_int.eq len (0 : usize))) then
    (pure ZERO)
  else
    let result : u64 ← coeffs[(← (len -? (1 : usize)))]_?;
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      len
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        (bb_add
          (← (bb_mul result point))
          (← coeffs[(← ((← (len -? (1 : usize))) -? i))]_?)) :
        RustM u64)))

end Plonky3_hax.Specs.Baby_bear


namespace Plonky3_hax.Specs.Merkle

--  Hash output size in bytes (256-bit digest).
def HASH_SIZE : usize := (32 : usize)

--  A Merkle tree root commitment.
abbrev MerkleRoot : Type := (RustArray u8 32)

--  A single node hash in the Merkle tree.
abbrev MerkleHash : Type := (RustArray u8 32)

--  Maximum Merkle tree depth. Baby Bear supports 2^27 roots of unity,
--  so 27 is a safe upper bound for Plonky3 tree depth.
def MAX_MERKLE_DEPTH : usize := (27 : usize)

--  A Merkle authentication path: sibling hashes from leaf to root.
--  `siblings[0]` is the sibling of the leaf; `siblings[depth - 1]` is
--  the sibling of the root's child. `depth` indicates how many entries
--  are valid.
structure MerklePath where
  siblings : (RustArray (RustArray u8 32) 27)
  depth : usize

@[reducible] instance Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes MerklePath
  where

instance Impl : Core_models.Clone.Clone MerklePath where
  clone := fun (self : MerklePath) => do
    (pure (MerklePath.mk
      (siblings := (MerklePath.siblings self))
      (depth := (MerklePath.depth self))))

--  Hash two child nodes to produce a parent node hash.
-- 
--  A byte-wise mixing function of `left` and `right`; it is not
--  collision-resistant.
def hash_two_to_one (left : (RustArray u8 32)) (right : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      HASH_SIZE
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        let l : u8 ← left[i]_?;
        let r : u8 ← right[i]_?;
        let result : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← ((← ((← (Core_models.Num.Impl_6.wrapping_add
                  (← (Core_models.Num.Impl_6.wrapping_mul
                    (← (Core_models.Num.Impl_6.wrapping_add l r))
                    (158 : u8)))
                  (← (Rust_primitives.Hax.cast_op i))))
                ^^^? (← (Core_models.Num.Impl_6.wrapping_mul l (109 : u8)))))
              ^^^? r)));
        (pure result) :
        RustM (RustArray u8 32))));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      HASH_SIZE
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          j
          (← ((← result[j]_?)
            ^^^? (← (Core_models.Num.Impl_6.wrapping_mul
              (← result[(← (j -? (1 : usize)))]_?)
              (197 : u8)))))) :
        RustM (RustArray u8 32))));
  (pure result)

--  Hash a leaf value (a Baby Bear field element, 8 bytes little-endian,
--  padded to 32 with a 0x00 domain separator).
def hash_leaf (value_bytes : (RustArray u8 8)) : RustM (RustArray u8 32) := do
  let input : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let input : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      input
      (0 : usize)
      (0 : u8));
  let input : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun input _ => (do (pure true) : RustM Bool))
      input
      (fun input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          input
          (← (i +? (1 : usize)))
          (← value_bytes[i]_?)) :
        RustM (RustArray u8 32))));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      HASH_SIZE
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result k =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          k
          (← ((← (Core_models.Num.Impl_6.wrapping_mul
              (← (Core_models.Num.Impl_6.wrapping_add (← input[k]_?) (55 : u8)))
              (191 : u8)))
            ^^^? (← input[(← ((← (k +? (7 : usize))) %? HASH_SIZE))]_?)))) :
        RustM (RustArray u8 32))));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      HASH_SIZE
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result m =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          m
          (← (Core_models.Num.Impl_6.wrapping_add
            (← result[m]_?)
            (← (Core_models.Num.Impl_6.wrapping_mul
              (← result[(← (m -? (1 : usize)))]_?)
              (163 : u8)))))) :
        RustM (RustArray u8 32))));
  (pure result)

--  Serialize a Baby Bear field element (u64, canonical < p) to
--  little-endian bytes.
def field_elem_to_bytes (x : u64) : RustM (RustArray u8 8) := do
  (pure #v[(← (Rust_primitives.Hax.cast_op (← (x &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (8 : i32))) &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (16 : i32))) &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (24 : i32))) &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (32 : i32))) &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (40 : i32))) &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (48 : i32))) &&&? (255 : u64))))),
             (← (Rust_primitives.Hax.cast_op
               (← ((← (x >>>? (56 : i32))) &&&? (255 : u64)))))])

--  Hash a Baby Bear field element as a Merkle leaf.
def hash_field_elem (x : u64) : RustM (RustArray u8 32) := do
  (hash_leaf (← (field_elem_to_bytes x)))

--  Verify a Merkle authentication path.
-- 
--  At each level, if the current index bit is 0 the current hash is the
--  left child and the sibling is the right child; otherwise vice versa.
--  Returns true iff the recomputed root matches the expected root.
def merkle_verify_path
    (root : (RustArray u8 32))
    (leaf_hash : (RustArray u8 32))
    (index : u64)
    (path : MerklePath) :
    RustM Bool := do
  if
  (← (Rust_primitives.Hax.Machine_int.gt
    (MerklePath.depth path)
    MAX_MERKLE_DEPTH)) then
    (pure false)
  else
    let current : (RustArray u8 32) := leaf_hash;
    let idx : u64 := index;
    let ⟨current, idx⟩ ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (MerklePath.depth path)
        (fun ⟨current, idx⟩ _ => (do (pure true) : RustM Bool))
        (Rust_primitives.Hax.Tuple2.mk current idx)
        (fun ⟨current, idx⟩ level =>
          (do
          let sibling : (RustArray u8 32) ← (MerklePath.siblings path)[level]_?;
          let current : (RustArray u8 32) ←
            if
            (← (Rust_primitives.Hax.Machine_int.eq
              (← (idx &&&? (1 : u64)))
              (0 : u64))) then
              let current : (RustArray u8 32) ←
                (hash_two_to_one current sibling);
              (pure current)
            else
              let current : (RustArray u8 32) ←
                (hash_two_to_one sibling current);
              (pure current);
          let idx : u64 ← (idx >>>? (1 : i32));
          (pure (Rust_primitives.Hax.Tuple2.mk current idx)) :
          RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 32) u64))));
    let equal : Bool := true;
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      HASH_SIZE
      (fun equal _ => (do (pure true) : RustM Bool))
      equal
      (fun equal i =>
        (do
        if
        (← (Rust_primitives.Hax.Machine_int.ne (← current[i]_?) (← root[i]_?)))
        then
          let equal : Bool := false;
          (pure equal)
        else
          (pure equal) :
        RustM Bool)))

def merkle_build_root.MAX_LEAVES : usize := (1024 : usize)

def merkle_build_root.MAX_LOG_LEAVES : usize := (10 : usize)

--  Build a Merkle tree from leaf hashes and return the root.
-- 
--  Requires `num_leaves` to be `0` or a power of two with
--  `num_leaves <= 1024` and `num_leaves <= leaves.len()`; larger trees index
--  out of bounds.
def merkle_build_root
    (leaves : (RustSlice (RustArray u8 32)))
    (num_leaves : usize) :
    RustM (RustArray u8 32) := do
  if (← (Rust_primitives.Hax.Machine_int.eq num_leaves (0 : usize))) then
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize))
  else
    if (← (Rust_primitives.Hax.Machine_int.eq num_leaves (1 : usize))) then
      leaves[(0 : usize)]_?
    else
      let buf : (RustArray (RustArray u8 32) 1024) ←
        (Rust_primitives.Hax.repeat
          (← (Rust_primitives.Hax.repeat (0 : u8) (32 : usize)))
          (1024 : usize));
      let n_load : usize ←
        (Core_models.Cmp.Ord.min usize num_leaves merkle_build_root.MAX_LEAVES);
      let buf : (RustArray (RustArray u8 32) 1024) ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          n_load
          (fun buf _ => (do (pure true) : RustM Bool))
          buf
          (fun buf i =>
            (do
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              buf
              i
              (← leaves[i]_?)) :
            RustM (RustArray (RustArray u8 32) 1024))));
      let width : usize := num_leaves;
      let ⟨buf, width⟩ ←
        (Rust_primitives.Hax.Folds.fold_range_cf
          (0 : usize)
          merkle_build_root.MAX_LOG_LEAVES
          (fun ⟨buf, width⟩ _ => (do (pure true) : RustM Bool))
          (Rust_primitives.Hax.Tuple2.mk buf width)
          (fun ⟨buf, width⟩ _ =>
            (do
            if (← (Rust_primitives.Hax.Machine_int.le width (1 : usize))) then
              (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                (Rust_primitives.Hax.Tuple2.mk
                  Rust_primitives.Hax.Tuple0.mk
                  (Rust_primitives.Hax.Tuple2.mk buf width))))
            else
              let half : usize ← (width /? (2 : usize));
              let buf : (RustArray (RustArray u8 32) 1024) ←
                (Rust_primitives.Hax.Folds.fold_range
                  (0 : usize)
                  half
                  (fun buf _ => (do (pure true) : RustM Bool))
                  buf
                  (fun buf j =>
                    (do
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      buf
                      j
                      (← (hash_two_to_one
                        (← buf[(← ((2 : usize) *? j))]_?)
                        (← buf[
                          (← ((← ((2 : usize) *? j)) +? (1 : usize)))
                          ]_?)))) :
                    RustM (RustArray (RustArray u8 32) 1024))));
              let width : usize := half;
              (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
                (Rust_primitives.Hax.Tuple2.mk buf width))) :
            RustM
            (Core_models.Ops.Control_flow.ControlFlow
              (Rust_primitives.Hax.Tuple2
                Rust_primitives.Hax.Tuple0
                (Rust_primitives.Hax.Tuple2
                  (RustArray (RustArray u8 32) 1024)
                  usize))
              (Rust_primitives.Hax.Tuple2
                (RustArray (RustArray u8 32) 1024)
                usize)))));
      buf[(0 : usize)]_?

def merkle_build_and_prove.MAX_LEAVES : usize := (1024 : usize)

def merkle_build_and_prove.MAX_DEPTH : usize := (10 : usize)

--  Build a tree and extract the authentication path for a leaf index.
--  Used by the prover / tests.
def merkle_build_and_prove
    (leaves : (RustSlice (RustArray u8 32)))
    (num_leaves : usize)
    (leaf_index : usize) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 32) MerklePath) := do
  let path : MerklePath :=
    (MerklePath.mk
      (siblings := (← (Rust_primitives.Hax.repeat
        (← (Rust_primitives.Hax.repeat (0 : u8) (32 : usize)))
        (27 : usize))))
      (depth := (0 : usize)));
  if (← (Rust_primitives.Hax.Machine_int.le num_leaves (1 : usize))) then
    let root : (RustArray u8 32) ←
      if (← (Rust_primitives.Hax.Machine_int.eq num_leaves (1 : usize))) then
        leaves[(0 : usize)]_?
      else
        (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    (pure (Rust_primitives.Hax.Tuple2.mk root path))
  else
    let levels : (RustArray (RustArray (RustArray u8 32) 1024) 11) ←
      (Rust_primitives.Hax.repeat
        (← (Rust_primitives.Hax.repeat
          (← (Rust_primitives.Hax.repeat (0 : u8) (32 : usize)))
          (1024 : usize)))
        (11 : usize));
    let n_load : usize ←
      (Core_models.Cmp.Ord.min
        usize num_leaves merkle_build_and_prove.MAX_LEAVES);
    let levels : (RustArray (RustArray (RustArray u8 32) 1024) 11) ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        n_load
        (fun levels _ => (do (pure true) : RustM Bool))
        levels
        (fun levels i =>
          (do
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            levels
            (0 : usize)
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← levels[(0 : usize)]_?)
              i
              (← leaves[i]_?)))) :
          RustM (RustArray (RustArray (RustArray u8 32) 1024) 11))));
    let width : usize := num_leaves;
    let depth : usize := (0 : usize);
    let ⟨depth, levels, width⟩ ←
      (Rust_primitives.Hax.Folds.fold_range_cf
        (0 : usize)
        merkle_build_and_prove.MAX_DEPTH
        (fun ⟨depth, levels, width⟩ _ => (do (pure true) : RustM Bool))
        (Rust_primitives.Hax.Tuple3.mk depth levels width)
        (fun ⟨depth, levels, width⟩ _ =>
          (do
          if (← (Rust_primitives.Hax.Machine_int.le width (1 : usize))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Rust_primitives.Hax.Tuple2.mk
                Rust_primitives.Hax.Tuple0.mk
                (Rust_primitives.Hax.Tuple3.mk depth levels width))))
          else
            let half : usize ← (width /? (2 : usize));
            let levels : (RustArray (RustArray (RustArray u8 32) 1024) 11) ←
              (Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                half
                (fun levels _ => (do (pure true) : RustM Bool))
                levels
                (fun levels j =>
                  (do
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    levels
                    (← (depth +? (1 : usize)))
                    (←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      (← levels[(← (depth +? (1 : usize)))]_?)
                      j
                      (← (hash_two_to_one
                        (← (← levels[depth]_?)[(← ((2 : usize) *? j))]_?)
                        (← (← levels[depth]_?)[
                          (← ((← ((2 : usize) *? j)) +? (1 : usize)))
                          ]_?)))))) :
                  RustM (RustArray (RustArray (RustArray u8 32) 1024) 11))));
            let width : usize := half;
            let depth : usize ← (depth +? (1 : usize));
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (Rust_primitives.Hax.Tuple3.mk depth levels width))) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Rust_primitives.Hax.Tuple2
              Rust_primitives.Hax.Tuple0
              (Rust_primitives.Hax.Tuple3
                usize
                (RustArray (RustArray (RustArray u8 32) 1024) 11)
                usize))
            (Rust_primitives.Hax.Tuple3
              usize
              (RustArray (RustArray (RustArray u8 32) 1024) 11)
              usize)))));
    let idx : usize := leaf_index;
    let ⟨idx, path⟩ ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        depth
        (fun ⟨idx, path⟩ _ => (do (pure true) : RustM Bool))
        (Rust_primitives.Hax.Tuple2.mk idx path)
        (fun ⟨idx, path⟩ level =>
          (do
          let sibling_idx : usize ←
            if
            (← (Rust_primitives.Hax.Machine_int.eq
              (← (idx &&&? (1 : usize)))
              (0 : usize))) then
              (idx +? (1 : usize))
            else
              (idx -? (1 : usize));
          let path : MerklePath :=
            {path
            with siblings := (←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (MerklePath.siblings path)
              level
              (← (← levels[level]_?)[sibling_idx]_?)))};
          let idx : usize ← (idx >>>? (1 : i32));
          (pure (Rust_primitives.Hax.Tuple2.mk idx path)) :
          RustM (Rust_primitives.Hax.Tuple2 usize MerklePath))));
    let path : MerklePath := {path with depth := depth};
    let root : (RustArray u8 32) ← (← levels[depth]_?)[(0 : usize)]_?;
    (pure (Rust_primitives.Hax.Tuple2.mk root path))

end Plonky3_hax.Specs.Merkle


namespace Plonky3_hax.Specs.Poseidon2

--  Permutation width.
def WIDTH : usize := (16 : usize)

--  Number of full rounds per half.
def HALF_FULL_ROUNDS : usize := (4 : usize)

--  Number of partial rounds.
def PARTIAL_ROUNDS : usize := (13 : usize)

--  Round constants for the 4 initial external rounds. 4×16.
def RC16_EXTERNAL_INITIAL : (RustArray (RustArray u64 16) 4) :=
  RustM.of_isOk
    (do
    #v[#v[(1774958255 : u64),
            (1185780729 : u64),
            (1621102414 : u64),
            (1796380621 : u64),
            (588815102 : u64),
            (1932426223 : u64),
            (1925334750 : u64),
            (747903232 : u64),
            (89648862 : u64),
            (360728943 : u64),
            (977184635 : u64),
            (1425273457 : u64),
            (256487465 : u64),
            (1200041953 : u64),
            (572403254 : u64),
            (448208942 : u64)],
         #v[(1215789478 : u64),
              (944884184 : u64),
              (953948096 : u64),
              (547326025 : u64),
              (646827752 : u64),
              (889997530 : u64),
              (1536873262 : u64),
              (86189867 : u64),
              (1065944411 : u64),
              (32019634 : u64),
              (333311454 : u64),
              (456061748 : u64),
              (1963448500 : u64),
              (1827584334 : u64),
              (1391160226 : u64),
              (1348741381 : u64)],
         #v[(88424255 : u64),
              (104111868 : u64),
              (1763866748 : u64),
              (79691676 : u64),
              (1988915530 : u64),
              (1050669594 : u64),
              (359890076 : u64),
              (573163527 : u64),
              (222820492 : u64),
              (159256268 : u64),
              (669703072 : u64),
              (763177444 : u64),
              (889367200 : u64),
              (256335831 : u64),
              (704371273 : u64),
              (25886717 : u64)],
         #v[(51754520 : u64),
              (1833211857 : u64),
              (454499742 : u64),
              (1384520381 : u64),
              (777848065 : u64),
              (1053320300 : u64),
              (1851729162 : u64),
              (344647910 : u64),
              (401996362 : u64),
              (1046925956 : u64),
              (5351995 : u64),
              (1212119315 : u64),
              (754867989 : u64),
              (36972490 : u64),
              (751272725 : u64),
              (506915399 : u64)]])
    (by rfl)

--  Round constants for the 4 terminal external rounds. 4×16.
def RC16_EXTERNAL_FINAL : (RustArray (RustArray u64 16) 4) :=
  RustM.of_isOk
    (do
    #v[#v[(1922082829 : u64),
            (1870549801 : u64),
            (1502529704 : u64),
            (1990744480 : u64),
            (1700391016 : u64),
            (1702593455 : u64),
            (321330495 : u64),
            (528965731 : u64),
            (183414327 : u64),
            (1886297254 : u64),
            (1178602734 : u64),
            (1923111974 : u64),
            (744004766 : u64),
            (549271463 : u64),
            (1781349648 : u64),
            (542259047 : u64)],
         #v[(1536158148 : u64),
              (715456982 : u64),
              (503426110 : u64),
              (340311124 : u64),
              (1558555932 : u64),
              (1226350925 : u64),
              (742828095 : u64),
              (1338992758 : u64),
              (1641600456 : u64),
              (1843351545 : u64),
              (301835475 : u64),
              (43203215 : u64),
              (386838401 : u64),
              (1520185679 : u64),
              (1235297680 : u64),
              (904680097 : u64)],
         #v[(1491801617 : u64),
              (1581784677 : u64),
              (913384905 : u64),
              (247083962 : u64),
              (532844013 : u64),
              (107190701 : u64),
              (213827818 : u64),
              (1979521776 : u64),
              (1358282574 : u64),
              (1681743681 : u64),
              (1867507480 : u64),
              (1530706910 : u64),
              (507181886 : u64),
              (695185447 : u64),
              (1172395131 : u64),
              (1250800299 : u64)],
         #v[(1503161625 : u64),
              (817684387 : u64),
              (498481458 : u64),
              (494676004 : u64),
              (1404253825 : u64),
              (108246855 : u64),
              (59414691 : u64),
              (744214112 : u64),
              (890862029 : u64),
              (1342765939 : u64),
              (1417398904 : u64),
              (1897591937 : u64),
              (1066647396 : u64),
              (1682806907 : u64),
              (1015795079 : u64),
              (1619482808 : u64)]])
    (by rfl)

--  Round constants for the 13 partial (internal) rounds. Applied only to `state[0]`.
def RC16_INTERNAL : (RustArray u64 13) :=
  RustM.of_isOk
    (do
    #v[(1518359488 : u64),
         (1765533241 : u64),
         (945325693 : u64),
         (422793067 : u64),
         (311365592 : u64),
         (1311448267 : u64),
         (1629555936 : u64),
         (1009879353 : u64),
         (190525218 : u64),
         (786108885 : u64),
         (557776863 : u64),
         (212616710 : u64),
         (605745517 : u64)])
    (by rfl)

--  S-box: `x^7` over Baby Bear.
def sbox (x : u64) : RustM u64 := do
  let x2 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul x x);
  let x4 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul x2 x2);
  (Plonky3_hax.Specs.Baby_bear.bb_mul
    x4
    (← (Plonky3_hax.Specs.Baby_bear.bb_mul x2 x)))

--  Apply the 4×4 MDS `M_4 = circ(2, 3, 1, 1)` in place. Matches upstream
--  `apply_mat4`.
def apply_mat4 (x : (RustArray u64 4)) : RustM (RustArray u64 4) := do
  let t01 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← x[(0 : usize)]_?)
      (← x[(1 : usize)]_?));
  let t23 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← x[(2 : usize)]_?)
      (← x[(3 : usize)]_?));
  let t0123 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_add t01 t23);
  let t01123 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add t0123 (← x[(1 : usize)]_?));
  let t01233 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add t0123 (← x[(3 : usize)]_?));
  let two_x0 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← x[(0 : usize)]_?)
      (← x[(0 : usize)]_?));
  let two_x2 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← x[(2 : usize)]_?)
      (← x[(2 : usize)]_?));
  let new3 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_add t01233 two_x0);
  let new1 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_add t01123 two_x2);
  let new0 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_add t01123 t01);
  let new2 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_add t01233 t23);
  let x : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      x
      (0 : usize)
      new0);
  let x : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      x
      (1 : usize)
      new1);
  let x : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      x
      (2 : usize)
      new2);
  let x : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      x
      (3 : usize)
      new3);
  (pure x)

--  Apply the width-16 external MDS `M_E` in place. Matches upstream
--  `mds_light_permutation` with `WIDTH = 16`.
def mds_light_permutation_16 (state : (RustArray u64 16)) :
    RustM (RustArray u64 16) := do
  let chunk : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let ⟨chunk, state⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (WIDTH /? (4 : usize)))
      (fun ⟨chunk, state⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk chunk state)
      (fun ⟨chunk, state⟩ kk =>
        (do
        let k : usize ← (kk *? (4 : usize));
        let chunk : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            chunk
            (0 : usize)
            (← state[k]_?));
        let chunk : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            chunk
            (1 : usize)
            (← state[(← (k +? (1 : usize)))]_?));
        let chunk : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            chunk
            (2 : usize)
            (← state[(← (k +? (2 : usize)))]_?));
        let chunk : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            chunk
            (3 : usize)
            (← state[(← (k +? (3 : usize)))]_?));
        let chunk : (RustArray u64 4) ← (apply_mat4 chunk);
        let state : (RustArray u64 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            k
            (← chunk[(0 : usize)]_?));
        let state : (RustArray u64 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (k +? (1 : usize)))
            (← chunk[(1 : usize)]_?));
        let state : (RustArray u64 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (k +? (2 : usize)))
            (← chunk[(2 : usize)]_?));
        let state : (RustArray u64 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (k +? (3 : usize)))
            (← chunk[(3 : usize)]_?));
        (pure (Rust_primitives.Hax.Tuple2.mk chunk state)) :
        RustM
        (Rust_primitives.Hax.Tuple2 (RustArray u64 4) (RustArray u64 16)))));
  let sums : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let sums : (RustArray u64 4) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (4 : usize)
      (fun sums _ => (do (pure true) : RustM Bool))
      sums
      (fun sums kk =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          sums
          kk
          (← (Plonky3_hax.Specs.Baby_bear.bb_add
            (← (Plonky3_hax.Specs.Baby_bear.bb_add
              (← state[kk]_?)
              (← state[(← (kk +? (4 : usize)))]_?)))
            (← (Plonky3_hax.Specs.Baby_bear.bb_add
              (← state[(← (kk +? (8 : usize)))]_?)
              (← state[(← (kk +? (12 : usize)))]_?)))))) :
        RustM (RustArray u64 4))));
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      WIDTH
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          i
          (← (Plonky3_hax.Specs.Baby_bear.bb_add
            (← state[i]_?)
            (← sums[(← (i %? (4 : usize)))]_?)))) :
        RustM (RustArray u64 16))));
  (pure state)

--  Apply the internal `1 + diag(V)` matrix in place, given the precomputed
--  sum of the state. Matches upstream `internal_layer_mat_mul` for width 16.
-- 
--  Diagonal V (over Baby Bear):
--    `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27,
--      -1/2^8, -1/16, -1/2^27]`
-- 
--  Result: `state'[i] = sum + V[i] · state[i]` (since `M_I = 1 + diag(V)`).
def internal_mat_mul_16 (state : (RustArray u64 16)) (sum : u64) :
    RustM (RustArray u64 16) := do
  let two_s0 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← state[(0 : usize)]_?)
      (← state[(0 : usize)]_?));
  let new0 : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_sub sum two_s0);
  let new1 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add (← state[(1 : usize)]_?) sum);
  let new2 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_add
        (← state[(2 : usize)]_?)
        (← state[(2 : usize)]_?)))
      sum);
  let new3 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(3 : usize)]_?)
        (2 : u64)))
      sum);
  let new4 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_mul
        (3 : u64)
        (← state[(4 : usize)]_?))));
  let new5 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_mul
        (4 : u64)
        (← state[(5 : usize)]_?))));
  let new6 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(6 : usize)]_?)
        (2 : u64))));
  let new7 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_mul
        (3 : u64)
        (← state[(7 : usize)]_?))));
  let new8 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_mul
        (4 : u64)
        (← state[(8 : usize)]_?))));
  let new9 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(9 : usize)]_?)
        (256 : u64)))
      sum);
  let new10 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(10 : usize)]_?)
        (4 : u64)))
      sum);
  let new11 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(11 : usize)]_?)
        (8 : u64)))
      sum);
  let new12 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(12 : usize)]_?)
        (← ((1 : u64) <<<? (27 : i32)))))
      sum);
  let new13 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(13 : usize)]_?)
        (256 : u64))));
  let new14 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(14 : usize)]_?)
        (16 : u64))));
  let new15 : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      sum
      (← (Plonky3_hax.Specs.Baby_bear.bb_div
        (← state[(15 : usize)]_?)
        (← ((1 : u64) <<<? (27 : i32))))));
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (0 : usize)
      new0);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (1 : usize)
      new1);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (2 : usize)
      new2);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (3 : usize)
      new3);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (4 : usize)
      new4);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (5 : usize)
      new5);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (6 : usize)
      new6);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (7 : usize)
      new7);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (8 : usize)
      new8);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (9 : usize)
      new9);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (10 : usize)
      new10);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (11 : usize)
      new11);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (12 : usize)
      new12);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (13 : usize)
      new13);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (14 : usize)
      new14);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (15 : usize)
      new15);
  (pure state)

--  One full external round: add round constants, full-state S-box, MDS.
def external_round_16 (state : (RustArray u64 16)) (rc : (RustArray u64 16)) :
    RustM (RustArray u64 16) := do
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      WIDTH
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          i
          (← (sbox
            (← (Plonky3_hax.Specs.Baby_bear.bb_add
              (← state[i]_?)
              (← rc[i]_?)))))) :
        RustM (RustArray u64 16))));
  let state : (RustArray u64 16) ← (mds_light_permutation_16 state);
  (pure state)

--  One partial round: add round constant to `state[0]`, S-box `state[0]`,
--  then internal MDS.
def internal_round_16 (state : (RustArray u64 16)) (rc : u64) :
    RustM (RustArray u64 16) := do
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (0 : usize)
      (← (sbox
        (← (Plonky3_hax.Specs.Baby_bear.bb_add (← state[(0 : usize)]_?) rc)))));
  let sum : u64 := (0 : u64);
  let sum : u64 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      WIDTH
      (fun sum _ => (do (pure true) : RustM Bool))
      sum
      (fun sum i =>
        (do
        (Plonky3_hax.Specs.Baby_bear.bb_add sum (← state[i]_?)) : RustM u64)));
  let state : (RustArray u64 16) ← (internal_mat_mul_16 state sum);
  (pure state)

--  Apply the Poseidon2 permutation in place to a width-16 Baby Bear state.
-- 
--  Every cell must be canonical (in `[0, p)`). The result, as canonical
--  representatives, is that of `default_babybear_poseidon2_16().permute_mut`
--  in `p3-baby-bear` 0.5.
def poseidon2_permute_16 (state : (RustArray u64 16)) :
    RustM (RustArray u64 16) := do
  let state : (RustArray u64 16) ← (mds_light_permutation_16 state);
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      HALF_FULL_ROUNDS
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state r =>
        (do
        (external_round_16 state (← RC16_EXTERNAL_INITIAL[r]_?)) :
        RustM (RustArray u64 16))));
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      PARTIAL_ROUNDS
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state p =>
        (do
        (internal_round_16 state (← RC16_INTERNAL[p]_?)) :
        RustM (RustArray u64 16))));
  let state : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      HALF_FULL_ROUNDS
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state r =>
        (do
        (external_round_16 state (← RC16_EXTERNAL_FINAL[r]_?)) :
        RustM (RustArray u64 16))));
  (pure state)

end Plonky3_hax.Specs.Poseidon2


namespace Plonky3_hax.Air

--  A row-major trace matrix of Baby Bear field elements.
-- 
--  `cells[row * width + col]` is the field element at row `row`, column `col`.
structure Trace where
  width : usize
  height : usize
  cells : (Alloc.Vec.Vec u64 Alloc.Alloc.Global)

--  Create a new trace with the given dimensions, filled with zeros.
def Impl.zeros (width : usize) (height : usize) : RustM Trace := do
  (pure (Trace.mk
    (width := width)
    (height := height)
    (cells := (← (Alloc.Vec.from_elem u64 (0 : u64) (← (width *? height)))))))

--  Construct a trace from a row-major vector.
def Impl.from_cells
    (width : usize)
    (height : usize)
    (cells : (Alloc.Vec.Vec u64 Alloc.Alloc.Global)) :
    RustM Trace := do
  let _ ←
    match
      (Rust_primitives.Hax.Tuple2.mk
        (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global cells))
        (← (width *? height)))
    with
      | ⟨left_val, right_val⟩ =>
        (Hax_lib.assert
          (← (Rust_primitives.Hax.Machine_int.eq left_val right_val)));
  (pure (Trace.mk (width := width) (height := height) (cells := cells)))

--  Read the value at (row, col).
def Impl.get (self : Trace) (row : usize) (col : usize) : RustM u64 := do
  (Trace.cells self)[(← ((← (row *? (Trace.width self))) +? col))]_?

--  Write the value at (row, col).
def Impl.set (self : Trace) (row : usize) (col : usize) (val : u64) :
    RustM Trace := do
  let self : Trace :=
    {self
    with cells := (← (Alloc.Slice.Impl.to_vec
      (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        (← (Alloc.Vec.Impl_1.as_slice (Trace.cells self)))
        (← ((← (row *? (Trace.width self))) +? col))
        val))))};
  (pure self)

--  Borrow a row as a slice.
def Impl.row (self : Trace) (row : usize) : RustM (RustSlice u64) := do
  (Trace.cells self)[
    (Core_models.Ops.Range.Range.mk
      (start := (← (row *? (Trace.width self))))
      (_end := (← ((← (row +? (1 : usize))) *? (Trace.width self)))))
    ]_?

--  Fibonacci AIR's first constraint: `next[0] − cur[1]`.
def FIB_NEXT_A : usize := (0 : usize)

--  Fibonacci AIR's second constraint: `next[1] − (cur[0] + cur[1])`.
def FIB_NEXT_B : usize := (1 : usize)

--  Evaluate a transition constraint on two consecutive rows.
def eval_transition
    (kind : usize)
    (cur : (RustSlice u64))
    (next : (RustSlice u64)) :
    RustM u64 := do
  if (← (Rust_primitives.Hax.Machine_int.eq kind FIB_NEXT_A)) then
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      (← next[(0 : usize)]_?)
      (← cur[(1 : usize)]_?))
  else
    (Plonky3_hax.Specs.Baby_bear.bb_sub
      (← next[(1 : usize)]_?)
      (← (Plonky3_hax.Specs.Baby_bear.bb_add
        (← cur[(0 : usize)]_?)
        (← cur[(1 : usize)]_?))))

--  A transition constraint: a predicate on two consecutive rows.
-- 
--  The constraint holds at step `i` iff
--    `eval_transition(kind, trace.row(i), trace.row(i + 1)) == 0`.
structure TransitionConstraint where
  name : String
  kind : usize
  degree : usize

--  A boundary constraint: a claimed value at a specific (row, column).
structure BoundaryConstraint where
  row : usize
  col : usize
  value : u64

--  Full AIR specification.
structure AirSpec where
  num_columns : usize
  transitions : (Alloc.Vec.Vec TransitionConstraint Alloc.Alloc.Global)
  boundaries : (Alloc.Vec.Vec BoundaryConstraint Alloc.Alloc.Global)

--  Check all transition constraints on a trace.
-- 
--  Each transition constraint must evaluate to zero on every pair of
--  consecutive rows (there are `trace.height - 1` such pairs).
def check_transitions (air : AirSpec) (trace : Trace) : RustM Bool := do
  if
  (← (Rust_primitives.Hax.Machine_int.ne
    (Trace.width trace)
    (AirSpec.num_columns air))) then
    (pure false)
  else
    if
    (← (Rust_primitives.Hax.Machine_int.lt (Trace.height trace) (2 : usize)))
    then
      (pure true)
    else
      let ok : Bool := true;
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← ((Trace.height trace) -? (1 : usize)))
        (fun ok _ => (do (pure true) : RustM Bool))
        ok
        (fun ok i =>
          (do
          let row_i : (RustSlice u64) ← (Impl.row trace i);
          let row_next : (RustSlice u64) ←
            (Impl.row trace (← (i +? (1 : usize))));
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (← (Alloc.Vec.Impl_1.len TransitionConstraint Alloc.Alloc.Global
              (AirSpec.transitions air)))
            (fun ok _ => (do (pure true) : RustM Bool))
            ok
            (fun ok k =>
              (do
              let c : TransitionConstraint ← (AirSpec.transitions air)[k]_?;
              let v : u64 ←
                (eval_transition (TransitionConstraint.kind c) row_i row_next);
              if (← (Rust_primitives.Hax.Machine_int.ne v (0 : u64))) then
                let ok : Bool := false;
                (pure ok)
              else
                (pure ok) :
              RustM Bool))) :
          RustM Bool)))

--  Check all boundary constraints on a trace.
def check_boundaries (air : AirSpec) (trace : Trace) : RustM Bool := do
  let ok : Bool := true;
  let ok : Bool ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Alloc.Vec.Impl_1.len BoundaryConstraint Alloc.Alloc.Global
        (AirSpec.boundaries air)))
      (fun ok _ => (do (pure true) : RustM Bool))
      ok
      (fun ok i =>
        (do
        let b : BoundaryConstraint ← (AirSpec.boundaries air)[i]_?;
        if
        (← ((← (Rust_primitives.Hax.Machine_int.ge
            (BoundaryConstraint.row b)
            (Trace.height trace)))
          ||? (← (Rust_primitives.Hax.Machine_int.ge
            (BoundaryConstraint.col b)
            (Trace.width trace))))) then
          let ok : Bool := false;
          (pure ok)
        else
          if
          (← (Rust_primitives.Hax.Machine_int.ne
            (← (Impl.get
              trace
              (BoundaryConstraint.row b)
              (BoundaryConstraint.col b)))
            (BoundaryConstraint.value b))) then
            let ok : Bool := false;
            (pure ok)
          else
            (pure ok) :
        RustM Bool)));
  (pure ok)

--  Full trace-validity check: transitions and boundaries.
def trace_valid (air : AirSpec) (trace : Trace) : RustM Bool := do
  ((← (check_transitions air trace)) &&? (← (check_boundaries air trace)))

--  Width of the Fibonacci AIR trace (two columns: a and b).
def FIB_WIDTH : usize := (2 : usize)

--  Build the Fibonacci AIR specification.
-- 
--  Boundaries set `trace[0] = [0, 1]`, so successive rows contain
--  consecutive Fibonacci numbers (mod p).
def fib_air (_ : Rust_primitives.Hax.Tuple0) : RustM AirSpec := do
  (pure (AirSpec.mk
    (num_columns := FIB_WIDTH)
    (transitions := (← (Alloc.Slice.Impl.into_vec
      TransitionConstraint
      Alloc.Alloc.Global
      (← (Rust_primitives.unsize
        #v[(TransitionConstraint.mk
               (name := "next.a = cur.b")
               (kind := FIB_NEXT_A)
               (degree := (1 : usize))),
             (TransitionConstraint.mk
               (name := "next.b = cur.a + cur.b")
               (kind := FIB_NEXT_B)
               (degree := (1 : usize)))])))))
    (boundaries := (← (Alloc.Slice.Impl.into_vec
      BoundaryConstraint
      Alloc.Alloc.Global
      (← (Rust_primitives.unsize
        #v[(BoundaryConstraint.mk
               (row := (0 : usize))
               (col := (0 : usize))
               (value := (0 : u64))),
             (BoundaryConstraint.mk
               (row := (0 : usize))
               (col := (1 : usize))
               (value := (1 : u64)))])))))))

--  Generate a valid Fibonacci trace of `height` rows.
def fib_trace (height : usize) : RustM Trace := do
  let t : Trace ← (Impl.zeros FIB_WIDTH height);
  if (← (Rust_primitives.Hax.Machine_int.eq height (0 : usize))) then
    (pure t)
  else
    let t : Trace ← (Impl.set t (0 : usize) (0 : usize) (0 : u64));
    let t : Trace ← (Impl.set t (0 : usize) (1 : usize) (1 : u64));
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      height
      (fun t _ => (do (pure true) : RustM Bool))
      t
      (fun t i =>
        (do
        let a : u64 ← (Impl.get t (← (i -? (1 : usize))) (0 : usize));
        let b : u64 ← (Impl.get t (← (i -? (1 : usize))) (1 : usize));
        let t : Trace ← (Impl.set t i (0 : usize) b);
        let t : Trace ←
          (Impl.set
            t
            i
            (1 : usize)
            (← (Plonky3_hax.Specs.Baby_bear.bb_add a b)));
        (pure t) :
        RustM Trace)))

--  Maximum degree of all transition constraints in an AIR.
def air_max_degree (air : AirSpec) : RustM usize := do
  let d : usize := (0 : usize);
  let d : usize ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Alloc.Vec.Impl_1.len TransitionConstraint Alloc.Alloc.Global
        (AirSpec.transitions air)))
      (fun d _ => (do (pure true) : RustM Bool))
      d
      (fun d i =>
        (do
        if
        (← (Rust_primitives.Hax.Machine_int.gt
          (TransitionConstraint.degree (← (AirSpec.transitions air)[i]_?))
          d)) then
          let d : usize :=
            (TransitionConstraint.degree (← (AirSpec.transitions air)[i]_?));
          (pure d)
        else
          (pure d) :
        RustM usize)));
  (pure d)

end Plonky3_hax.Air


namespace Plonky3_hax.Fri

--  Maximum number of FRI layers (folding rounds).
-- 
--  Baby Bear admits 2^27 roots of unity, so tree depth <= 27.
def MAX_FRI_LAYERS : usize := (27 : usize)

--  Maximum number of query positions per round.
def MAX_FRI_QUERIES : usize := (64 : usize)

--  Maximum remainder-polynomial degree (the final layer is checked directly).
def MAX_REMAINDER_DEGREE : usize := (16 : usize)

--  FRI protocol options.
structure FriOptions where
  num_layers : usize
  domain_log2 : u32
  num_queries : usize
  blowup : usize
  coset_shift : u64
  proof_of_work_bits : u32

@[instance] opaque Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes FriOptions :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  Core_models.Clone.Clone FriOptions :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes FriOptions :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Marker.Copy FriOptions :=
  by constructor <;> exact Inhabited.default

--  A single query response for one FRI layer.
-- 
--  The prover supplies: the evaluation at the queried point, the evaluation
--  at its sibling (negation), and Merkle authentication paths for both.
structure FriLayerQuery where
  eval_pos : u64
  eval_neg : u64
  path_pos : Plonky3_hax.Specs.Merkle.MerklePath
  path_neg : Plonky3_hax.Specs.Merkle.MerklePath
  index_pos : u64
  index_neg : u64

--  A complete FRI layer: Merkle root plus per-query responses.
structure FriLayer where
  commitment : (RustArray u8 32)
  queries : (Alloc.Vec.Vec FriLayerQuery Alloc.Alloc.Global)

--  The remainder polynomial, sent explicitly after all folding rounds.
structure FriRemainder where
  coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global)

--  A complete FRI proof.
structure FriProof where
  layers : (Alloc.Vec.Vec FriLayer Alloc.Alloc.Global)
  remainder : FriRemainder

--  Compute the FRI fold at one query.
-- 
--  Given `eval_pos = p(x)`, `eval_neg = p(-x)`, the query point `x`, and
--  the verifier challenge `alpha`, returns `p'(x^2)`.
def fri_fold (eval_pos : u64) (eval_neg : u64) (x : u64) (alpha : u64) :
    RustM u64 := do
  let sum : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_add eval_pos eval_neg);
  let diff : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_sub eval_pos eval_neg);
  let two : u64 := (2 : u64);
  let inv_two : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_inv two);
  let two_x : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul two x);
  let inv_two_x : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_inv two_x);
  let p_even : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul sum inv_two);
  let p_odd : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul diff inv_two_x);
  (Plonky3_hax.Specs.Baby_bear.bb_add
    p_even
    (← (Plonky3_hax.Specs.Baby_bear.bb_mul alpha p_odd)))

--  Compute the domain element at a given index.
-- 
--  The domain is `{omega^0, omega^1, ..., omega^(n-1)}`, where
--  `omega = bb_root_of_unity(domain_log2)`.
def domain_element (domain_log2 : u32) (index : u64) : RustM u64 := do
  let omega : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity domain_log2);
  (Plonky3_hax.Specs.Baby_bear.bb_pow omega index)

--  Coset variant of [`domain_element`]: returns the `index`-th element
--  of the coset `shift · K`, where `K` is the 2-adic subgroup of order
--  `2^domain_log2`. Equal to `shift * domain_element(domain_log2, index)`.
def coset_element (shift : u64) (domain_log2 : u32) (index : u64) :
    RustM u64 := do
  (Plonky3_hax.Specs.Baby_bear.bb_mul
    shift
    (← (domain_element domain_log2 index)))

--  Given an index in a domain of size 2^k, return the index of its negation.
-- 
--  Since omega^(n/2) = -1 in a primitive 2^k-th root domain, the sibling
--  of i is `(i + n/2) mod n`.
def sibling_index (index : u64) (domain_log2 : u32) : RustM u64 := do
  let n : u64 ← ((1 : u64) <<<? domain_log2);
  let half_n : u64 ← (n >>>? (1 : i32));
  ((← (index +? half_n)) &&&? (← (n -? (1 : u64))))

--  Compute the folded-domain index for `index`.
-- 
--  When folding x -> x^2, in a domain with generator omega indices i and
--  i + n/2 both map to the same element in the squared domain.
def folded_index (index : u64) (domain_log2 : u32) : RustM u64 := do
  let half_n : u64 ← ((1 : u64) <<<? (← (domain_log2 -? (1 : u32))));
  (index &&&? (← (half_n -? (1 : u64))))

--  Fold a polynomial's coefficients with challenge alpha.
-- 
--  `p'(y) = p_even(y) + alpha * p_odd(y)` in coefficient form.
def fold_polynomial (coeffs : (RustSlice u64)) (alpha : u64) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let n : usize ← (Core_models.Slice.Impl.len u64 coeffs);
  let half : usize ← (Core_models.Num.Impl_11.div_ceil n (2 : usize));
  let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.from_elem u64 (0 : u64) half);
  let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      half
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        let even_coeff : u64 ← coeffs[(← ((2 : usize) *? i))]_?;
        let odd_coeff : u64 ←
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← ((← ((2 : usize) *? i)) +? (1 : usize)))
            n)) then
            coeffs[(← ((← ((2 : usize) *? i)) +? (1 : usize)))]_?
          else
            (pure (0 : u64));
        let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Slice.Impl.to_vec
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← (Alloc.Vec.Impl_1.as_slice result))
              i
              (← (Plonky3_hax.Specs.Baby_bear.bb_add
                even_coeff
                (← (Plonky3_hax.Specs.Baby_bear.bb_mul alpha odd_coeff)))))));
        (pure result) :
        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
  (pure result)

--  Verify one FRI layer transition.
-- 
--  For each query, checks:
--  1. Merkle path for p(x) is valid under the layer commitment.
--  2. Merkle path for p(-x) is valid under the layer commitment.
--  3. `index_neg` is the sibling of `index_pos` in the domain.
--  4. The folded value matches the corresponding next-layer claimed evaluation.
def fri_verify_layer
    (layer : FriLayer)
    (next_eval_at_query : (RustSlice u64))
    (alpha : u64)
    (domain_log2 : u32)
    (shift : u64) :
    RustM Bool := do
  let num_queries : usize ←
    (Alloc.Vec.Impl_1.len FriLayerQuery Alloc.Alloc.Global
      (FriLayer.queries layer));
  match
    (← (Rust_primitives.Hax.Folds.fold_range_return
      (0 : usize)
      num_queries
      (fun _ _ => (do (pure true) : RustM Bool))
      Rust_primitives.Hax.Tuple0.mk
      (fun _ i =>
        (do
        let query : FriLayerQuery ← (FriLayer.queries layer)[i]_?;
        let leaf_pos : (RustArray u8 32) ←
          (Plonky3_hax.Specs.Merkle.hash_field_elem
            (FriLayerQuery.eval_pos query));
        if
        (← (Core_models.Ops.Bit.Not.not
          (← (Plonky3_hax.Specs.Merkle.merkle_verify_path
            (FriLayer.commitment layer)
            leaf_pos
            (FriLayerQuery.index_pos query)
            (FriLayerQuery.path_pos query))))) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Core_models.Ops.Control_flow.ControlFlow.Break false)))
        else
          let leaf_neg : (RustArray u8 32) ←
            (Plonky3_hax.Specs.Merkle.hash_field_elem
              (FriLayerQuery.eval_neg query));
          if
          (← (Core_models.Ops.Bit.Not.not
            (← (Plonky3_hax.Specs.Merkle.merkle_verify_path
              (FriLayer.commitment layer)
              leaf_neg
              (FriLayerQuery.index_neg query)
              (FriLayerQuery.path_neg query))))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Core_models.Ops.Control_flow.ControlFlow.Break false)))
          else
            let expected_neg : u64 ←
              (sibling_index (FriLayerQuery.index_pos query) domain_log2);
            if
            (← (Rust_primitives.Hax.Machine_int.ne
              (FriLayerQuery.index_neg query)
              expected_neg)) then
              (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                (Core_models.Ops.Control_flow.ControlFlow.Break false)))
            else
              let x : u64 ←
                (coset_element
                  shift
                  domain_log2
                  (FriLayerQuery.index_pos query));
              let folded : u64 ←
                (fri_fold
                  (FriLayerQuery.eval_pos query)
                  (FriLayerQuery.eval_neg query)
                  x
                  alpha);
              if
              (← ((← (Rust_primitives.Hax.Machine_int.lt
                  i
                  (← (Core_models.Slice.Impl.len u64 next_eval_at_query))))
                &&? (← (Rust_primitives.Hax.Machine_int.ne
                  folded
                  (← next_eval_at_query[i]_?))))) then
                (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                  (Core_models.Ops.Control_flow.ControlFlow.Break false)))
              else
                (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
                  Rust_primitives.Hax.Tuple0.mk)) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Core_models.Ops.Control_flow.ControlFlow
            Bool
            (Rust_primitives.Hax.Tuple2
              Rust_primitives.Hax.Tuple0
              Rust_primitives.Hax.Tuple0))
          Rust_primitives.Hax.Tuple0)))))
  with
    | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
    | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) => (pure true)

--  Verify a complete FRI proof.
-- 
--  Walks the layers, checks each transition, and verifies the final layer
--  against the remainder polynomial. Returns true iff all checks pass.
def fri_verify
    (proof : FriProof)
    (alphas : (RustSlice u64))
    (options : FriOptions) :
    RustM Bool := do
  let num_layers : usize ←
    (Alloc.Vec.Impl_1.len FriLayer Alloc.Alloc.Global (FriProof.layers proof));
  if
  (← (Rust_primitives.Hax.Machine_int.ne
    num_layers
    (FriOptions.num_layers options))) then
    (pure false)
  else
    if
    (← (Rust_primitives.Hax.Machine_int.lt
      (← (Core_models.Slice.Impl.len u64 alphas))
      num_layers)) then
      (pure false)
    else
      if (← (Rust_primitives.Hax.Machine_int.eq num_layers (0 : usize))) then
        (pure false)
      else
        let current_domain_log2 : u32 := (FriOptions.domain_log2 options);
        let current_shift : u64 := (FriOptions.coset_shift options);
        match
          (← (Rust_primitives.Hax.Folds.fold_range_return
            (0 : usize)
            num_layers
            (fun ⟨current_domain_log2, current_shift⟩ _ =>
              (do (pure true) : RustM Bool))
            (Rust_primitives.Hax.Tuple2.mk current_domain_log2 current_shift)
            (fun ⟨current_domain_log2, current_shift⟩ layer_idx =>
              (do
              let layer : FriLayer ← (FriProof.layers proof)[layer_idx]_?;
              let alpha : u64 ← alphas[layer_idx]_?;
              let num_queries : usize ←
                (Alloc.Vec.Impl_1.len FriLayerQuery Alloc.Alloc.Global
                  (FriLayer.queries layer));
              if
              (← (Rust_primitives.Hax.Machine_int.ne
                num_queries
                (FriOptions.num_queries options))) then
                (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                  (Core_models.Ops.Control_flow.ControlFlow.Break false)))
              else
                let next_domain_log2 : u32 ← (current_domain_log2 -? (1 : u32));
                let next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                  (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk);
                let next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                  if
                  (← (Rust_primitives.Hax.Machine_int.lt
                    (← (layer_idx +? (1 : usize)))
                    num_layers)) then
                    let next_layer : FriLayer ←
                      (FriProof.layers proof)[(← (layer_idx +? (1 : usize)))]_?;
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      num_queries
                      (fun next_evals _ => (do (pure true) : RustM Bool))
                      next_evals
                      (fun next_evals q =>
                        (do
                        if
                        (← (Rust_primitives.Hax.Machine_int.lt
                          q
                          (← (Alloc.Vec.Impl_1.len
                            FriLayerQuery
                            Alloc.Alloc.Global (FriLayer.queries next_layer)))))
                        then
                          let
                            next_evals : (Alloc.Vec.Vec
                              u64
                              Alloc.Alloc.Global) ←
                            (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                              next_evals
                              (FriLayerQuery.eval_pos
                                (← (FriLayer.queries next_layer)[q]_?)));
                          (pure next_evals)
                        else
                          (pure next_evals) :
                        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))))
                  else
                    let next_shift : u64 ←
                      (Plonky3_hax.Specs.Baby_bear.bb_mul
                        current_shift
                        current_shift);
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      num_queries
                      (fun next_evals _ => (do (pure true) : RustM Bool))
                      next_evals
                      (fun next_evals q =>
                        (do
                        let x_index : u64 ←
                          (folded_index
                            (FriLayerQuery.index_pos
                              (← (FriLayer.queries layer)[q]_?))
                            current_domain_log2);
                        let x_squared : u64 ←
                          (coset_element next_shift next_domain_log2 x_index);
                        let remainder_eval : u64 ←
                          (Plonky3_hax.Specs.Baby_bear.bb_poly_eval
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                              (FriRemainder.coeffs (FriProof.remainder proof))))
                            x_squared);
                        let
                          next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                          (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                            next_evals
                            remainder_eval);
                        (pure next_evals) :
                        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
                if
                (← (Core_models.Ops.Bit.Not.not
                  (← (fri_verify_layer
                    layer
                    (← (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global) next_evals))
                    alpha
                    current_domain_log2
                    current_shift)))) then
                  (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                    (Core_models.Ops.Control_flow.ControlFlow.Break false)))
                else
                  let current_domain_log2 : u32 := next_domain_log2;
                  let current_shift : u64 ←
                    (Plonky3_hax.Specs.Baby_bear.bb_mul
                      current_shift
                      current_shift);
                  (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
                    (Rust_primitives.Hax.Tuple2.mk
                      current_domain_log2
                      current_shift))) :
              RustM
              (Core_models.Ops.Control_flow.ControlFlow
                (Core_models.Ops.Control_flow.ControlFlow
                  Bool
                  (Rust_primitives.Hax.Tuple2
                    Rust_primitives.Hax.Tuple0
                    (Rust_primitives.Hax.Tuple2 u32 u64)))
                (Rust_primitives.Hax.Tuple2 u32 u64))))))
        with
          | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
          | (Core_models.Ops.Control_flow.ControlFlow.Continue
               ⟨current_domain_log2, current_shift⟩) =>
            let max_remainder_deg : usize := MAX_REMAINDER_DEGREE;
            if
            (← (Rust_primitives.Hax.Machine_int.gt
              (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
                (FriRemainder.coeffs (FriProof.remainder proof))))
              (← (max_remainder_deg +? (1 : usize))))) then
              match
                (← (Rust_primitives.Hax.Folds.fold_range_return
                  (← (max_remainder_deg +? (1 : usize)))
                  (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
                    (FriRemainder.coeffs (FriProof.remainder proof))))
                  (fun _ _ => (do (pure true) : RustM Bool))
                  Rust_primitives.Hax.Tuple0.mk
                  (fun _ k =>
                    (do
                    if
                    (← (Rust_primitives.Hax.Machine_int.ne
                      (← (FriRemainder.coeffs (FriProof.remainder proof))[k]_?)
                      (0 : u64))) then
                      (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                        (Core_models.Ops.Control_flow.ControlFlow.Break false)))
                    else
                      (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
                        Rust_primitives.Hax.Tuple0.mk)) :
                    RustM
                    (Core_models.Ops.Control_flow.ControlFlow
                      (Core_models.Ops.Control_flow.ControlFlow
                        Bool
                        (Rust_primitives.Hax.Tuple2
                          Rust_primitives.Hax.Tuple0
                          Rust_primitives.Hax.Tuple0))
                      Rust_primitives.Hax.Tuple0)))))
              with
                | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) =>
                  (pure ret)
                | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) =>
                  (pure true)
            else
              (pure true)

--  Evaluate a polynomial on a domain and build the Merkle commitment.
--  Used by the prover / tests.
def commit_polynomial (coeffs : (RustSlice u64)) (domain_log2 : u32) :
    RustM
    (Rust_primitives.Hax.Tuple3
      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
      (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global)
      (RustArray u8 32))
    := do
  let n : usize ← ((1 : usize) <<<? domain_log2);
  let omega : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity domain_log2);
  let evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.from_elem u64 (0 : u64) n);
  let hashes : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
    (Alloc.Vec.from_elem (RustArray u8 32)
      (← (Rust_primitives.Hax.repeat (0 : u8) (32 : usize)))
      n);
  let point : u64 := Plonky3_hax.Specs.Baby_bear.ONE;
  let ⟨evals, hashes, point⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      n
      (fun ⟨evals, hashes, point⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple3.mk evals hashes point)
      (fun ⟨evals, hashes, point⟩ i =>
        (do
        let evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Slice.Impl.to_vec
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← (Alloc.Vec.Impl_1.as_slice evals))
              i
              (← (Plonky3_hax.Specs.Baby_bear.bb_poly_eval coeffs point)))));
        let hashes : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
          (Alloc.Slice.Impl.to_vec
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← (Alloc.Vec.Impl_1.as_slice hashes))
              i
              (← (Plonky3_hax.Specs.Merkle.hash_field_elem (← evals[i]_?))))));
        let point : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul point omega);
        (pure (Rust_primitives.Hax.Tuple3.mk evals hashes point)) :
        RustM
        (Rust_primitives.Hax.Tuple3
          (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
          (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global)
          u64))));
  let root : (RustArray u8 32) ←
    (Plonky3_hax.Specs.Merkle.merkle_build_root
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) hashes))
      n);
  (pure (Rust_primitives.Hax.Tuple3.mk evals hashes root))

end Plonky3_hax.Fri


namespace Plonky3_hax.Ntt

--  Reverse the low `log_n` bits of `i`.
def bit_reverse (i : u64) (log_n : u32) : RustM u64 := do
  let x : u64 := i;
  let r : u64 := (0 : u64);
  let ⟨r, x⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : u32)
      log_n
      (fun ⟨r, x⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk r x)
      (fun ⟨r, x⟩ _ =>
        (do
        let r : u64 ←
          (Rust_primitives.Hax.Machine_int.bitor
            (← (r <<<? (1 : i32)))
            (← (x &&&? (1 : u64))));
        let x : u64 ← (x >>>? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk r x)) :
        RustM (Rust_primitives.Hax.Tuple2 u64 u64))));
  (pure r)

--  Forward NTT: evaluations of a polynomial at `{ω^0, ..., ω^(n-1)}` from
--  its coefficient sequence in monomial order. In place.
-- 
--  `omega` must be a primitive `n`-th root of unity in Baby Bear, where
--  `n = vals.len()` is a power of two.
def ntt (vals : (RustSlice u64)) (omega : u64) : RustM (RustSlice u64) := do
  let n : usize ← (Core_models.Slice.Impl.len u64 vals);
  let vals : (RustSlice u64) ←
    if (← (Rust_primitives.Hax.Machine_int.gt n (1 : usize))) then
      let log_n : u32 ← (Core_models.Num.Impl_11.trailing_zeros n);
      let vals : (RustSlice u64) ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          n
          (fun vals _ => (do (pure true) : RustM Bool))
          vals
          (fun vals i =>
            (do
            let j : usize ←
              (Rust_primitives.Hax.cast_op
                (← (bit_reverse (← (Rust_primitives.Hax.cast_op i)) log_n)));
            if (← (Rust_primitives.Hax.Machine_int.lt i j)) then
              let vals : (RustSlice u64) ←
                (Core_models.Slice.Impl.swap u64 vals i j);
              (pure vals)
            else
              (pure vals) :
            RustM (RustSlice u64))));
      (Rust_primitives.Hax.Folds.fold_range
        (0 : u32)
        log_n
        (fun vals _ => (do (pure true) : RustM Bool))
        vals
        (fun vals layer =>
          (do
          let size : usize ← ((1 : usize) <<<? (← (layer +? (1 : u32))));
          let half : usize ← (size /? (2 : usize));
          let w_size : u64 ←
            (Plonky3_hax.Specs.Baby_bear.bb_pow
              omega
              (← (Rust_primitives.Hax.cast_op (← (n /? size)))));
          let n_blocks : usize ← (n /? size);
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            n_blocks
            (fun vals _ => (do (pure true) : RustM Bool))
            vals
            (fun vals b =>
              (do
              let block : usize ← (b *? size);
              (Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                half
                (fun vals _ => (do (pure true) : RustM Bool))
                vals
                (fun vals j =>
                  (do
                  let w_pow : u64 ←
                    (Plonky3_hax.Specs.Baby_bear.bb_pow
                      w_size
                      (← (Rust_primitives.Hax.cast_op j)));
                  let t : u64 ←
                    (Plonky3_hax.Specs.Baby_bear.bb_mul
                      w_pow
                      (← vals[(← ((← (block +? j)) +? half))]_?));
                  let vals : (RustSlice u64) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      vals
                      (← ((← (block +? j)) +? half))
                      (← (Plonky3_hax.Specs.Baby_bear.bb_sub
                        (← vals[(← (block +? j))]_?)
                        t)));
                  let vals : (RustSlice u64) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      vals
                      (← (block +? j))
                      (← (Plonky3_hax.Specs.Baby_bear.bb_add
                        (← vals[(← (block +? j))]_?)
                        t)));
                  (pure vals) :
                  RustM (RustSlice u64)))) :
              RustM (RustSlice u64)))) :
          RustM (RustSlice u64))))
    else
      (pure vals);
  (pure vals)

--  Inverse NTT: coefficient sequence from evaluations at `{ω^0, ..., ω^(n-1)}`.
--  In place. `omega` is the same primitive root used in [`ntt`].
def intt (vals : (RustSlice u64)) (omega : u64) : RustM (RustSlice u64) := do
  let n : usize ← (Core_models.Slice.Impl.len u64 vals);
  let vals : (RustSlice u64) ←
    if (← (Rust_primitives.Hax.Machine_int.gt n (1 : usize))) then
      let omega_inv : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_inv omega);
      let vals : (RustSlice u64) ← (ntt vals omega_inv);
      let n_inv : u64 ←
        (Plonky3_hax.Specs.Baby_bear.bb_inv
          (← (Rust_primitives.Hax.cast_op n)));
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        n
        (fun vals _ => (do (pure true) : RustM Bool))
        vals
        (fun vals i =>
          (do
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            vals
            i
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul (← vals[i]_?) n_inv))) :
          RustM (RustSlice u64))))
    else
      (pure vals);
  (pure vals)

end Plonky3_hax.Ntt


namespace Plonky3_hax.Fri

--  Build a real FRI proof for one column's LDE evaluations.
-- 
--  `column_lde` is the size-`n` vector of evaluations of the column's
--  polynomial on the coset `options.coset_shift · K_n`, where
--  `n = 2^options.domain_log2`.
-- 
--  `alphas[i]` is the verifier challenge for fold `i`; the slice must
--  have at least `options.num_layers` entries.
-- 
--  `query_indices` are the verifier's chosen layer-0 query positions
--  in `[0, n)`; the slice length must equal `options.num_queries`.
-- 
--  Returns `None` if any dimension precondition is violated.
def fri_prove_column
    (column_lde : (RustSlice u64))
    (options : FriOptions)
    (alphas : (RustSlice u64))
    (query_indices : (RustSlice u64)) :
    RustM (Core_models.Option.Option FriProof) := do
  let n : usize ← (Core_models.Slice.Impl.len u64 column_lde);
  if
  (← (Rust_primitives.Hax.Machine_int.ne
    n
    (← ((1 : usize) <<<? (FriOptions.domain_log2 options))))) then
    (pure Core_models.Option.Option.None)
  else
    if
    (← (Rust_primitives.Hax.Machine_int.lt
      (← (Core_models.Slice.Impl.len u64 alphas))
      (FriOptions.num_layers options))) then
      (pure Core_models.Option.Option.None)
    else
      if
      (← (Rust_primitives.Hax.Machine_int.ne
        (← (Core_models.Slice.Impl.len u64 query_indices))
        (FriOptions.num_queries options))) then
        (pure Core_models.Option.Option.None)
      else
        if
        (← (Rust_primitives.Hax.Machine_int.eq
          (FriOptions.num_layers options)
          (0 : usize))) then
          (pure Core_models.Option.Option.None)
        else
          if
          (← (Rust_primitives.Hax.Machine_int.gt
            (← (Rust_primitives.Hax.cast_op (FriOptions.num_layers options)))
            (FriOptions.domain_log2 options))) then
            (pure Core_models.Option.Option.None)
          else
            let current_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
              (Alloc.Slice.Impl.to_vec u64 column_lde);
            let current_log2 : u32 := (FriOptions.domain_log2 options);
            let current_shift : u64 := (FriOptions.coset_shift options);
            let current_query_indices : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
              (Alloc.Slice.Impl.to_vec u64 query_indices);
            let layers : (Alloc.Vec.Vec FriLayer Alloc.Alloc.Global) ←
              (Alloc.Vec.Impl.with_capacity FriLayer
                (FriOptions.num_layers options));
            let
              ⟨current_evals,
               current_log2,
               current_query_indices,
               current_shift,
               layers⟩ ←
              (Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                (FriOptions.num_layers options)
                (fun
                  ⟨current_evals,
                   current_log2,
                   current_query_indices,
                   current_shift,
                   layers⟩
                  _ =>
                  (do (pure true) : RustM Bool))
                (Rust_primitives.Hax.Tuple5.mk
                  current_evals
                  current_log2
                  current_query_indices
                  current_shift
                  layers)
                (fun
                  ⟨current_evals,
                   current_log2,
                   current_query_indices,
                   current_shift,
                   layers⟩
                  layer_idx =>
                  (do
                  let m : usize ←
                    (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global current_evals);
                  let
                    leaves : (Alloc.Vec.Vec
                      (RustArray u8 32)
                      Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl.with_capacity (RustArray u8 32) m);
                  let
                    leaves : (Alloc.Vec.Vec
                      (RustArray u8 32)
                      Alloc.Alloc.Global) ←
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      m
                      (fun leaves _ => (do (pure true) : RustM Bool))
                      leaves
                      (fun leaves i =>
                        (do
                        (Alloc.Vec.Impl_1.push
                          (RustArray u8 32)
                          Alloc.Alloc.Global
                          leaves
                          (← (Plonky3_hax.Specs.Merkle.hash_field_elem
                            (← current_evals[i]_?)))) :
                        RustM
                        (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global))));
                  let commitment : (RustArray u8 32) ←
                    (Plonky3_hax.Specs.Merkle.merkle_build_root
                      (← (Core_models.Ops.Deref.Deref.deref
                        (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global)
                        leaves))
                      m);
                  let
                    queries : (Alloc.Vec.Vec FriLayerQuery Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl.with_capacity FriLayerQuery
                      (FriOptions.num_queries options));
                  let
                    queries : (Alloc.Vec.Vec FriLayerQuery Alloc.Alloc.Global) ←
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      (FriOptions.num_queries options)
                      (fun queries _ => (do (pure true) : RustM Bool))
                      queries
                      (fun queries q =>
                        (do
                        let i_pos : u64 ← current_query_indices[q]_?;
                        let i_neg : u64 ← (sibling_index i_pos current_log2);
                        let ⟨_, path_pos⟩ ←
                          (Plonky3_hax.Specs.Merkle.merkle_build_and_prove
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec
                                (RustArray u8 32)
                                Alloc.Alloc.Global) leaves))
                            m
                            (← (Rust_primitives.Hax.cast_op i_pos)));
                        let ⟨_, path_neg⟩ ←
                          (Plonky3_hax.Specs.Merkle.merkle_build_and_prove
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec
                                (RustArray u8 32)
                                Alloc.Alloc.Global) leaves))
                            m
                            (← (Rust_primitives.Hax.cast_op i_neg)));
                        let
                          queries : (Alloc.Vec.Vec
                            FriLayerQuery
                            Alloc.Alloc.Global) ←
                          (Alloc.Vec.Impl_1.push
                            FriLayerQuery
                            Alloc.Alloc.Global
                            queries
                            (FriLayerQuery.mk
                              (eval_pos := (← current_evals[
                                (← (Rust_primitives.Hax.cast_op i_pos))
                                ]_?))
                              (eval_neg := (← current_evals[
                                (← (Rust_primitives.Hax.cast_op i_neg))
                                ]_?))
                              (path_pos := path_pos)
                              (path_neg := path_neg)
                              (index_pos := i_pos)
                              (index_neg := i_neg)));
                        (pure queries) :
                        RustM
                        (Alloc.Vec.Vec FriLayerQuery Alloc.Alloc.Global))));
                  let layers : (Alloc.Vec.Vec FriLayer Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl_1.push FriLayer Alloc.Alloc.Global
                      layers
                      (FriLayer.mk
                        (commitment := commitment)
                        (queries := queries)));
                  let alpha : u64 ← alphas[layer_idx]_?;
                  let next_size : usize ← (m /? (2 : usize));
                  let next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                    (Alloc.Vec.from_elem u64 (0 : u64) next_size);
                  let next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      next_size
                      (fun next_evals _ => (do (pure true) : RustM Bool))
                      next_evals
                      (fun next_evals i =>
                        (do
                        let x : u64 ←
                          (coset_element
                            current_shift
                            current_log2
                            (← (Rust_primitives.Hax.cast_op i)));
                        let
                          next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                          (Alloc.Slice.Impl.to_vec
                            (←
                            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                              (← (Alloc.Vec.Impl_1.as_slice next_evals))
                              i
                              (← (fri_fold
                                (← current_evals[i]_?)
                                (← current_evals[(← (i +? next_size))]_?)
                                x
                                alpha)))));
                        (pure next_evals) :
                        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
                  let
                    next_query_indices : (Alloc.Vec.Vec
                      u64
                      Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl.with_capacity u64
                      (FriOptions.num_queries options));
                  let
                    next_query_indices : (Alloc.Vec.Vec
                      u64
                      Alloc.Alloc.Global) ←
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      (FriOptions.num_queries options)
                      (fun next_query_indices _ =>
                        (do (pure true) : RustM Bool))
                      next_query_indices
                      (fun next_query_indices q =>
                        (do
                        (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                          next_query_indices
                          (← (folded_index
                            (← current_query_indices[q]_?)
                            current_log2))) :
                        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
                  let current_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) :=
                    next_evals;
                  let current_log2 : u32 ← (current_log2 -? (1 : u32));
                  let current_shift : u64 ←
                    (Plonky3_hax.Specs.Baby_bear.bb_mul
                      current_shift
                      current_shift);
                  let
                    current_query_indices : (Alloc.Vec.Vec
                      u64
                      Alloc.Alloc.Global) :=
                    next_query_indices;
                  (pure (Rust_primitives.Hax.Tuple5.mk
                    current_evals
                    current_log2
                    current_query_indices
                    current_shift
                    layers)) :
                  RustM
                  (Rust_primitives.Hax.Tuple5
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                    u32
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                    u64
                    (Alloc.Vec.Vec FriLayer Alloc.Alloc.Global)))));
            let remaining_size : usize ←
              (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global current_evals);
            let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) :=
              current_evals;
            let coeffs : Rust_primitives.Hax.Tuple0 ←
              if
              (← (Rust_primitives.Hax.Machine_int.gt
                remaining_size
                (1 : usize))) then
                let omega : u64 ←
                  (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity current_log2);
                let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                  (Alloc.Slice.Impl.to_vec
                    (← (Plonky3_hax.Ntt.intt
                      (← (Alloc.Vec.Impl_1.as_slice coeffs))
                      omega)));
                if
                (← (Rust_primitives.Hax.Machine_int.ne current_shift (1 : u64)))
                then
                  let shift_inv : u64 ←
                    (Plonky3_hax.Specs.Baby_bear.bb_inv current_shift);
                  let shift_inv_pow : u64 := (1 : u64);
                  let ⟨coeffs, shift_inv_pow⟩ ←
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      remaining_size
                      (fun ⟨coeffs, shift_inv_pow⟩ _ =>
                        (do (pure true) : RustM Bool))
                      (Rust_primitives.Hax.Tuple2.mk coeffs shift_inv_pow)
                      (fun ⟨coeffs, shift_inv_pow⟩ i =>
                        (do
                        let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                          (Alloc.Slice.Impl.to_vec
                            (←
                            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                              (← (Alloc.Vec.Impl_1.as_slice coeffs))
                              i
                              (← (Plonky3_hax.Specs.Baby_bear.bb_mul
                                (← coeffs[i]_?)
                                shift_inv_pow)))));
                        let shift_inv_pow : u64 ←
                          (Plonky3_hax.Specs.Baby_bear.bb_mul
                            shift_inv_pow
                            shift_inv);
                        (pure (Rust_primitives.Hax.Tuple2.mk
                          coeffs
                          shift_inv_pow)) :
                        RustM
                        (Rust_primitives.Hax.Tuple2
                          (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                          u64))));
                  (pure coeffs)
                else
                  (pure coeffs)
              else
                (pure coeffs);
            (pure (Core_models.Option.Option.Some
              (FriProof.mk
                (layers := layers)
                (remainder := (FriRemainder.mk (coeffs := coeffs))))))

end Plonky3_hax.Fri


namespace Plonky3_hax.Quotient

--  Vanishing polynomial `Z_H(x) = x^h − 1`, where `h = 2^trace_log2`.
--  Zero exactly on the trace subgroup `H = {ω_h^0, …, ω_h^{h-1}}`.
def vanishing_poly_eval (x : u64) (trace_log2 : u32) : RustM u64 := do
  let h : u64 ← ((1 : u64) <<<? trace_log2);
  (Plonky3_hax.Specs.Baby_bear.bb_sub
    (← (Plonky3_hax.Specs.Baby_bear.bb_pow x h))
    (1 : u64))

--  Inverse of the vanishing polynomial, defined only when `x ∉ H`. The
--  caller is responsible for that precondition; on `H`, `Z_H` is zero
--  and `bb_inv` returns 0 (the canonical "undefined" sentinel).
def vanishing_poly_inv (x : u64) (trace_log2 : u32) : RustM u64 := do
  (Plonky3_hax.Specs.Baby_bear.bb_inv (← (vanishing_poly_eval x trace_log2)))

--  "All-but-last-row" selector
--  `Z'_H(x) = Z_H(x) / (x − ω_h^{h-1})`, which is zero exactly on the
--  rows `0 .. h-2` and nonzero at row `h-1`.
-- 
--  Plonky3's quotient uses this selector instead of the full `Z_H`
--  because for cyclic AIRs (like Fibonacci) the transition constraint
--  is only required to vanish on the first `h-1` rows; the wraparound
--  at row `h-1` is not required, and dividing by `Z_H` would force
--  the prover to satisfy a stricter condition than the AIR demands.
-- 
--  Computed without polynomial long-division:
--  `Z'_H(x) = (x^h − 1) / (x − ω_h^{h-1})`.
--  At `x ∉ H`, `Z_H(x) ≠ 0` and `(x − ω_h^{h-1}) ≠ 0`, so the division
--  is well-defined in the field.
def vanishing_selector_eval (x : u64) (trace_log2 : u32) : RustM u64 := do
  let omega_h : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity trace_log2);
  let h : u64 ← ((1 : u64) <<<? trace_log2);
  let omega_last : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_pow omega_h (← (h -? (1 : u64))));
  (Plonky3_hax.Specs.Baby_bear.bb_mul
    (← (vanishing_poly_eval x trace_log2))
    (← (Plonky3_hax.Specs.Baby_bear.bb_inv
      (← (Plonky3_hax.Specs.Baby_bear.bb_sub x omega_last)))))

--  Inverse of `vanishing_selector_eval`, defined when `x ∉ {ω_h^0, …, ω_h^{h-2}}`.
def vanishing_selector_inv (x : u64) (trace_log2 : u32) : RustM u64 := do
  (Plonky3_hax.Specs.Baby_bear.bb_inv
    (← (vanishing_selector_eval x trace_log2)))

--  Derive `num_constraints` deterministic random challenges for the
--  constraint LC, mixed from the trace commitment bytes. Same hash-style
--  derivation as `derive_fri_alphas`, but with a distinct domain
--  separator (`"C"` byte before each constraint index) so the FRI and
--  quotient challenge streams don't collide.
def derive_constraint_alphas
    (trace_commitment : (RustArray u8 32))
    (num_constraints : usize) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u64 num_constraints);
  let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_constraints
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result k =>
        (do
        let acc : u64 := (0 : u64);
        let acc : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_add
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
            (67 : u64));
        let acc : u64 ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            Plonky3_hax.Specs.Merkle.HASH_SIZE
            (fun acc _ => (do (pure true) : RustM Bool))
            acc
            (fun acc b =>
              (do
              let v : u64 ←
                (Rust_primitives.Hax.cast_op (← trace_commitment[b]_?));
              let acc : u64 ←
                (Plonky3_hax.Specs.Baby_bear.bb_add
                  (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
                  v);
              (pure acc) :
              RustM u64)));
        let acc : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_add
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
            (← (Rust_primitives.Hax.cast_op k)));
        let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global result acc);
        (pure result) :
        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
  (pure result)

--  Helper: read row `j` of the LDE as a `Vec<u64>` of length `width`.
def lde_row (lde : (RustSlice u64)) (j : usize) (width : usize) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let r : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u64 width);
  let r : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      width
      (fun r _ => (do (pure true) : RustM Bool))
      r
      (fun r c =>
        (do
        (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
          r
          (← lde[(← ((← (j *? width)) +? c))]_?)) :
        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
  (pure r)

--  Evaluate the linear combination of AIR transition constraints at LDE
--  row `j`. The "next row" for transition purposes is row `j + n/h`
--  (mod n), since the trace shift `g = ω_h` corresponds to a stride of
--  `n/h` in the LDE indexing.
def compute_constraint_lde_value
    (lde : (RustSlice u64))
    (j : usize)
    (air : Plonky3_hax.Air.AirSpec)
    (alphas : (RustSlice u64))
    (width : usize)
    (n : usize)
    (n_over_h : usize) :
    RustM u64 := do
  let cur : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ← (lde_row lde j width);
  let next : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (lde_row lde (← ((← (j +? n_over_h)) %? n)) width);
  let acc : u64 := (0 : u64);
  let limit : usize ←
    (Core_models.Cmp.Ord.min
      usize
      (← (Alloc.Vec.Impl_1.len
        Plonky3_hax.Air.TransitionConstraint
        Alloc.Alloc.Global (Plonky3_hax.Air.AirSpec.transitions air)))
      (← (Core_models.Slice.Impl.len u64 alphas)));
  let acc : u64 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      limit
      (fun acc _ => (do (pure true) : RustM Bool))
      acc
      (fun acc k =>
        (do
        let c : Plonky3_hax.Air.TransitionConstraint ←
          (Plonky3_hax.Air.AirSpec.transitions air)[k]_?;
        let v : u64 ←
          (Plonky3_hax.Air.eval_transition
            (Plonky3_hax.Air.TransitionConstraint.kind c)
            (← (Core_models.Ops.Deref.Deref.deref
              (Alloc.Vec.Vec u64 Alloc.Alloc.Global) cur))
            (← (Core_models.Ops.Deref.Deref.deref
              (Alloc.Vec.Vec u64 Alloc.Alloc.Global) next)));
        let acc : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_add
            acc
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul (← alphas[k]_?) v)));
        (pure acc) :
        RustM u64)));
  (pure acc)

--  Compute the quotient polynomial's evaluations on the LDE coset
--  `shift · K_n`: for each `j` in `[0, n)` the value
--  `Q(x_j) = C(x_j) / Z'_H(x_j)`, where `x_j = shift · ω_n^j` and `C` is
--  the `α`-combination of the AIR transition constraints. When `shift` is
--  not in the 2-adic subgroup, `Z'_H(x_j) ≠ 0` for every `j`.
-- 
--  Returns an empty `Vec` if preconditions fail (trace_log2 > domain_log2,
--  width mismatch, n not the LDE size).
def compute_quotient_lde
    (lde : (RustSlice u64))
    (air : Plonky3_hax.Air.AirSpec)
    (alphas : (RustSlice u64))
    (width : usize)
    (domain_log2 : u32)
    (trace_log2 : u32)
    (shift : u64) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  if
  (← ((← (Rust_primitives.Hax.Machine_int.gt trace_log2 domain_log2))
    ||? (← (Rust_primitives.Hax.Machine_int.ne
      width
      (Plonky3_hax.Air.AirSpec.num_columns air))))) then
    (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk)
  else
    let n : usize ← ((1 : usize) <<<? domain_log2);
    let h : usize ← ((1 : usize) <<<? trace_log2);
    if
    (← (Rust_primitives.Hax.Machine_int.ne
      (← (Core_models.Slice.Impl.len u64 lde))
      (← (n *? width)))) then
      (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk)
    else
      if (← (Rust_primitives.Hax.Machine_int.ne (← (n %? h)) (0 : usize))) then
        (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk)
      else
        let n_over_h : usize ← (n /? h);
        let q : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl.with_capacity u64 n);
        let omega_n : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity domain_log2);
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          n
          (fun q _ => (do (pure true) : RustM Bool))
          q
          (fun q j =>
            (do
            let x_j : u64 ←
              (Plonky3_hax.Specs.Baby_bear.bb_mul
                shift
                (← (Plonky3_hax.Specs.Baby_bear.bb_pow
                  omega_n
                  (← (Rust_primitives.Hax.cast_op j)))));
            let c_j : u64 ←
              (compute_constraint_lde_value lde j air alphas width n n_over_h);
            let inv : u64 ← (vanishing_selector_inv x_j trace_log2);
            let q : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
              (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                q
                (← (Plonky3_hax.Specs.Baby_bear.bb_mul c_j inv)));
            (pure q) :
            RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))))

--  Merkle-commit the quotient LDE values, leaf-hashing each `u64`.
def commit_quotient_lde (q_lde : (RustSlice u64)) :
    RustM (RustArray u8 32) := do
  let n : usize ← (Core_models.Slice.Impl.len u64 q_lde);
  if (← (Rust_primitives.Hax.Machine_int.eq n (0 : usize))) then
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize))
  else
    let leaves : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
      (Alloc.Vec.Impl.with_capacity (RustArray u8 32) n);
    let leaves : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        n
        (fun leaves _ => (do (pure true) : RustM Bool))
        leaves
        (fun leaves i =>
          (do
          (Alloc.Vec.Impl_1.push (RustArray u8 32) Alloc.Alloc.Global
            leaves
            (← (Plonky3_hax.Specs.Merkle.hash_field_elem (← q_lde[i]_?)))) :
          RustM (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global))));
    (Plonky3_hax.Specs.Merkle.merkle_build_root
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) leaves))
      n)

end Plonky3_hax.Quotient


namespace Plonky3_hax.Ood

--  Derive a deterministic OOD point from the quotient commitment.
-- 
--  For `counter = 0, 1, …, 63` the candidate is the base-257 accumulation
--  in F_p of the byte `0x7A`, the 32 commitment bytes and `counter`; the
--  first candidate that is nonzero and satisfies `Z_H(z) ≠ 0` is returned,
--  and `GENERATOR` if none is. Membership of `z` in the LDE coset is not
--  checked, and `domain_log2` is unused.
def derive_ood_point
    (quotient_commitment : (RustArray u8 32))
    (trace_log2 : u32)
    (domain_log2 : u32) :
    RustM u64 := do
  let _ := domain_log2;
  match
    (← (Rust_primitives.Hax.Folds.fold_range_return
      (0 : u64)
      (64 : u64)
      (fun _ _ => (do (pure true) : RustM Bool))
      Rust_primitives.Hax.Tuple0.mk
      (fun _ counter =>
        (do
        let acc : u64 := (0 : u64);
        let acc : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_add
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
            (122 : u64));
        let acc : u64 ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            Plonky3_hax.Specs.Merkle.HASH_SIZE
            (fun acc _ => (do (pure true) : RustM Bool))
            acc
            (fun acc b =>
              (do
              (Plonky3_hax.Specs.Baby_bear.bb_add
                (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
                (← (Rust_primitives.Hax.cast_op (← quotient_commitment[b]_?))))
              :
              RustM u64)));
        let acc : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_add
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
            counter);
        if
        (← ((← (Rust_primitives.Hax.Machine_int.ne acc (0 : u64)))
          &&? (← (Rust_primitives.Hax.Machine_int.ne
            (← (Plonky3_hax.Quotient.vanishing_poly_eval acc trace_log2))
            (0 : u64))))) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Core_models.Ops.Control_flow.ControlFlow.Break acc)))
        else
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            Rust_primitives.Hax.Tuple0.mk)) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Core_models.Ops.Control_flow.ControlFlow
            u64
            (Rust_primitives.Hax.Tuple2
              Rust_primitives.Hax.Tuple0
              Rust_primitives.Hax.Tuple0))
          Rust_primitives.Hax.Tuple0)))))
  with
    | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
    | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) =>
      (pure Plonky3_hax.Specs.Baby_bear.GENERATOR)

--  Evaluate every column of the trace polynomial at `z`.
-- 
--  For each column `c`, the trace values `[T_c(ω_h^0), …, T_c(ω_h^{h-1})]`
--  are INTTed to recover the column polynomial's coefficients, which are
--  then Horner-evaluated at `z`. Returns one field element per column.
-- 
--  Requires `trace.height` to be a power of two.
def evaluate_trace_at (trace : Plonky3_hax.Air.Trace) (z : u64) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let h : usize := (Plonky3_hax.Air.Trace.height trace);
  let w : usize := (Plonky3_hax.Air.Trace.width trace);
  let out : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u64 w);
  if
  (← ((← (Rust_primitives.Hax.Machine_int.eq h (0 : usize)))
    ||? (← (Rust_primitives.Hax.Machine_int.ne
      (← (h &&&? (← (h -? (1 : usize)))))
      (0 : usize))))) then
    (pure out)
  else
    let trace_log2 : u32 ← (Core_models.Num.Impl_11.trailing_zeros h);
    let omega_h : u64 ←
      (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity trace_log2);
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      w
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out col =>
        (do
        let evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl.with_capacity u64 h);
        let evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            h
            (fun evals _ => (do (pure true) : RustM Bool))
            evals
            (fun evals i =>
              (do
              (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                evals
                (← (Plonky3_hax.Air.Impl.get trace i col))) :
              RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
        let evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Slice.Impl.to_vec
            (← (Plonky3_hax.Ntt.intt
              (← (Alloc.Vec.Impl_1.as_slice evals))
              omega_h)));
        let v : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_poly_eval
            (← (Core_models.Ops.Deref.Deref.deref
              (Alloc.Vec.Vec u64 Alloc.Alloc.Global) evals))
            z);
        let out : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global out v);
        (pure out) :
        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))))

--  Evaluate the quotient polynomial at `z` given its evaluations on the
--  LDE coset `shift · K_n`.
-- 
--  The values are interpolated with the inverse NTT as evaluations of
--  `Q(shift · x)` on `K_n`; the `i`-th coefficient is then multiplied by
--  `shift^{-i}` to obtain the coefficients of `Q`, which are evaluated at
--  `z` by Horner's rule. Returns `0` when `q_lde.len() != 2^domain_log2`.
def evaluate_quotient_at
    (q_lde : (RustSlice u64))
    (domain_log2 : u32)
    (shift : u64)
    (z : u64) :
    RustM u64 := do
  let n : usize ← (Core_models.Slice.Impl.len u64 q_lde);
  if
  (← (Rust_primitives.Hax.Machine_int.ne n (← ((1 : usize) <<<? domain_log2))))
  then
    (pure (0 : u64))
  else
    let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
      (Alloc.Slice.Impl.to_vec u64 q_lde);
    let omega_n : u64 ←
      (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity domain_log2);
    let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
      (Alloc.Slice.Impl.to_vec
        (← (Plonky3_hax.Ntt.intt
          (← (Alloc.Vec.Impl_1.as_slice coeffs))
          omega_n)));
    let shift_inv : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_inv shift);
    let shift_inv_pow : u64 := (1 : u64);
    let ⟨coeffs, shift_inv_pow⟩ ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        n
        (fun ⟨coeffs, shift_inv_pow⟩ _ => (do (pure true) : RustM Bool))
        (Rust_primitives.Hax.Tuple2.mk coeffs shift_inv_pow)
        (fun ⟨coeffs, shift_inv_pow⟩ i =>
          (do
          let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
            (Alloc.Slice.Impl.to_vec
              (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                (← (Alloc.Vec.Impl_1.as_slice coeffs))
                i
                (← (Plonky3_hax.Specs.Baby_bear.bb_mul
                  (← coeffs[i]_?)
                  shift_inv_pow)))));
          let shift_inv_pow : u64 ←
            (Plonky3_hax.Specs.Baby_bear.bb_mul shift_inv_pow shift_inv);
          (pure (Rust_primitives.Hax.Tuple2.mk coeffs shift_inv_pow)) :
          RustM
          (Rust_primitives.Hax.Tuple2
            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
            u64))));
    (Plonky3_hax.Specs.Baby_bear.bb_poly_eval
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u64 Alloc.Alloc.Global) coeffs))
      z)

end Plonky3_hax.Ood


namespace Plonky3_hax.Pow

--  Encode a `u64` nonce as a 32-byte hash input. Little-endian in the
--  low 8 bytes; remaining 24 bytes are zero.
def nonce_to_hash (nonce : u64) : RustM (RustArray u8 32) := do
  let out : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let n : u64 := nonce;
  let ⟨n, out⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun ⟨n, out⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk n out)
      (fun ⟨n, out⟩ i =>
        (do
        let out : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            out
            i
            (← (Rust_primitives.Hax.cast_op (← (n &&&? (255 : u64))))));
        let n : u64 ← (n >>>? (8 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk n out)) :
        RustM (Rust_primitives.Hax.Tuple2 u64 (RustArray u8 32)))));
  (pure out)

def leading_zero_bits.NOT_FOUND : u32 := Core_models.Num.Impl_8.MAX

--  Count the number of leading zero bits in a hash, big-endian.
-- 
--  Encoding choice: one `u32` state variable that holds either
--  `u32::MAX` ("haven't yet found a set bit") or the final answer.
--  Once a set bit is located the state does not change. The Lean
--  translation lifts one mutable variable per loop; two variables
--  (`count` and `done`) would need a tuple accumulator.
def leading_zero_bits (h : (RustArray u8 32)) : RustM u32 := do
  let result : u32 := leading_zero_bits.NOT_FOUND;
  let result : u32 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      Plonky3_hax.Specs.Merkle.HASH_SIZE
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        if
        (← (Rust_primitives.Hax.Machine_int.eq
          result
          leading_zero_bits.NOT_FOUND)) then
          let b : u8 ← h[i]_?;
          if (← (Rust_primitives.Hax.Machine_int.ne b (0 : u8))) then
            (Rust_primitives.Hax.Folds.fold_range
              (0 : u32)
              (8 : u32)
              (fun result _ => (do (pure true) : RustM Bool))
              result
              (fun result j =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.eq
                  result
                  leading_zero_bits.NOT_FOUND)) then
                  let mask : u8 ← ((1 : u8) <<<? (← ((7 : u32) -? j)));
                  if
                  (← (Rust_primitives.Hax.Machine_int.ne
                    (← (b &&&? mask))
                    (0 : u8))) then
                    let result : u32 ←
                      ((← ((← (Rust_primitives.Hax.cast_op i)) *? (8 : u32)))
                        +? j);
                    (pure result)
                  else
                    (pure result)
                else
                  (pure result) :
                RustM u32)))
          else
            (pure result)
        else
          (pure result) :
        RustM u32)));
  if
  (← (Rust_primitives.Hax.Machine_int.eq result leading_zero_bits.NOT_FOUND))
  then
    (Rust_primitives.Hax.cast_op
      (← (Plonky3_hax.Specs.Merkle.HASH_SIZE *? (8 : usize))))
  else
    (pure result)

--  Brute-force search for a nonce satisfying the PoW condition.
-- 
--  Returns the smallest `nonce ∈ [0, max_iter)` such that
--  `leading_zero_bits(hash_two_to_one(seed, nonce_to_hash(nonce))) ≥ bits`.
--  Returns `None` if no nonce in the range works.
-- 
--  `max_iter` caps the search to keep test runtimes bounded; in practice
--  the verifier's `bits` parameter is much smaller than `log2(max_iter)`,
--  so this loop always finds a nonce well before the cap.
def grind_pow_nonce (seed : (RustArray u8 32)) (bits : u32) (max_iter : u64) :
    RustM (Core_models.Option.Option u64) := do
  if (← (Rust_primitives.Hax.Machine_int.gt bits (64 : u32))) then
    (pure Core_models.Option.Option.None)
  else
    match
      (← (Rust_primitives.Hax.Folds.fold_range_return
        (0 : u64)
        max_iter
        (fun _ _ => (do (pure true) : RustM Bool))
        Rust_primitives.Hax.Tuple0.mk
        (fun _ nonce =>
          (do
          let h : (RustArray u8 32) ←
            (Plonky3_hax.Specs.Merkle.hash_two_to_one
              seed
              (← (nonce_to_hash nonce)));
          if
          (← (Rust_primitives.Hax.Machine_int.ge
            (← (leading_zero_bits h))
            bits)) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Core_models.Ops.Control_flow.ControlFlow.Break
                (Core_models.Option.Option.Some nonce))))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              Rust_primitives.Hax.Tuple0.mk)) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Core_models.Ops.Control_flow.ControlFlow
              (Core_models.Option.Option u64)
              (Rust_primitives.Hax.Tuple2
                Rust_primitives.Hax.Tuple0
                Rust_primitives.Hax.Tuple0))
            Rust_primitives.Hax.Tuple0)))))
    with
      | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
      | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) =>
        (pure Core_models.Option.Option.None)

--  Verifier-side PoW check: re-hash `(seed, nonce)` and confirm at least
--  `bits` leading zero bits.
def verify_pow_nonce (seed : (RustArray u8 32)) (nonce : u64) (bits : u32) :
    RustM Bool := do
  if (← (Rust_primitives.Hax.Machine_int.gt bits (64 : u32))) then
    (pure false)
  else
    let h : (RustArray u8 32) ←
      (Plonky3_hax.Specs.Merkle.hash_two_to_one seed (← (nonce_to_hash nonce)));
    (Rust_primitives.Hax.Machine_int.ge (← (leading_zero_bits h)) bits)

end Plonky3_hax.Pow


namespace Plonky3_hax.Deep

--  Derive the DEEP-batching challenge `β` from the quotient commitment.
--  Same Fiat-Shamir style as the other challenges, but with the 'D'
--  domain separator so the streams stay disjoint.
def derive_deep_beta (quotient_commitment : (RustArray u8 32)) : RustM u64 := do
  let acc : u64 := (0 : u64);
  let acc : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_add
      (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
      (68 : u64));
  let acc : u64 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      Plonky3_hax.Specs.Merkle.HASH_SIZE
      (fun acc _ => (do (pure true) : RustM Bool))
      acc
      (fun acc b =>
        (do
        (Plonky3_hax.Specs.Baby_bear.bb_add
          (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
          (← (Rust_primitives.Hax.cast_op (← quotient_commitment[b]_?)))) :
        RustM u64)));
  (pure acc)

--  Compute the DEEP polynomial's LDE values: `DEEP_P[j] = (P_lde[j] − v) / (x_j − z)`,
--  where `x_j = shift · ω_n^j` is the LDE coset point at index `j`.
def compute_deep_poly_lde
    (p_lde : (RustSlice u64))
    (claimed_value : u64)
    (z : u64)
    (domain_log2 : u32)
    (shift : u64) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let n : usize ← (Core_models.Slice.Impl.len u64 p_lde);
  let deep : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u64 n);
  let deep : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      n
      (fun deep _ => (do (pure true) : RustM Bool))
      deep
      (fun deep j =>
        (do
        let x_j : u64 ←
          (Plonky3_hax.Fri.coset_element
            shift
            domain_log2
            (← (Rust_primitives.Hax.cast_op j)));
        let numerator : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_sub (← p_lde[j]_?) claimed_value);
        let denominator_inv : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_inv
            (← (Plonky3_hax.Specs.Baby_bear.bb_sub x_j z)));
        let deep : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
            deep
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul numerator denominator_inv)));
        (pure deep) :
        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
  (pure deep)

--  Batched LC: `B[j] = Σ_i β^i · DEEP_{P_i}[j]`.
def combine_deep_polys
    (deeps : (RustSlice (Alloc.Vec.Vec u64 Alloc.Alloc.Global)))
    (beta : u64) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  if
  (← (Core_models.Slice.Impl.is_empty (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
    deeps)) then
    (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk)
  else
    let n : usize ←
      (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global (← deeps[(0 : usize)]_?));
    let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
      (Alloc.Vec.from_elem u64 (0 : u64) n);
    let beta_pow : u64 := (1 : u64);
    let ⟨beta_pow, result⟩ ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← (Core_models.Slice.Impl.len (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
          deeps))
        (fun ⟨beta_pow, result⟩ _ => (do (pure true) : RustM Bool))
        (Rust_primitives.Hax.Tuple2.mk beta_pow result)
        (fun ⟨beta_pow, result⟩ i =>
          (do
          let d : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ← deeps[i]_?;
          let bound : usize ←
            (Core_models.Cmp.Ord.min
              usize n (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global d)));
          let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              bound
              (fun result _ => (do (pure true) : RustM Bool))
              result
              (fun result j =>
                (do
                (Alloc.Slice.Impl.to_vec
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← (Alloc.Vec.Impl_1.as_slice result))
                    j
                    (← (Plonky3_hax.Specs.Baby_bear.bb_add
                      (← result[j]_?)
                      (← (Plonky3_hax.Specs.Baby_bear.bb_mul
                        beta_pow
                        (← d[j]_?)))))))) :
                RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
          let beta_pow : u64 ←
            (Plonky3_hax.Specs.Baby_bear.bb_mul beta_pow beta);
          (pure (Rust_primitives.Hax.Tuple2.mk beta_pow result)) :
          RustM
          (Rust_primitives.Hax.Tuple2
            u64
            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)))));
    (pure result)

--  Reconstruct the DEEP-batched LC value at LDE point `x_q` from the
--  opened polynomial values at the same point and the claimed OOD
--  evaluations. The verifier uses this to cross-check the DEEP FRI
--  proof's first-layer query against the column-FRI openings.
-- 
--  `p_openings[i]` is the opened value of `P_i` at `x_q`,
--  `claimed_values[i]` is `P_i(z)` from the OOD claim,
--  `x_q` is the LDE point, `z` is the OOD challenge,
--  `beta` is the DEEP-batching challenge.
def reconstruct_deep_value_at
    (p_openings : (RustSlice u64))
    (claimed_values : (RustSlice u64))
    (x_q : u64)
    (z : u64)
    (beta : u64) :
    RustM u64 := do
  let denom_inv : u64 ←
    (Plonky3_hax.Specs.Baby_bear.bb_inv
      (← (Plonky3_hax.Specs.Baby_bear.bb_sub x_q z)));
  let result : u64 := (0 : u64);
  let beta_pow : u64 := (1 : u64);
  let bound : usize ←
    (Core_models.Cmp.Ord.min
      usize
      (← (Core_models.Slice.Impl.len u64 p_openings))
      (← (Core_models.Slice.Impl.len u64 claimed_values)));
  let ⟨beta_pow, result⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      bound
      (fun ⟨beta_pow, result⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk beta_pow result)
      (fun ⟨beta_pow, result⟩ i =>
        (do
        let deep_i : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_mul
            (← (Plonky3_hax.Specs.Baby_bear.bb_sub
              (← p_openings[i]_?)
              (← claimed_values[i]_?)))
            denom_inv);
        let result : u64 ←
          (Plonky3_hax.Specs.Baby_bear.bb_add
            result
            (← (Plonky3_hax.Specs.Baby_bear.bb_mul beta_pow deep_i)));
        let beta_pow : u64 ← (Plonky3_hax.Specs.Baby_bear.bb_mul beta_pow beta);
        (pure (Rust_primitives.Hax.Tuple2.mk beta_pow result)) :
        RustM (Rust_primitives.Hax.Tuple2 u64 u64))));
  (pure result)

end Plonky3_hax.Deep


namespace Plonky3_hax.Plonky3

--  A proof of the reference STARK.
structure Plonky3Proof where
  trace_commitment : (RustArray u8 32)
  quotient_commitment : (RustArray u8 32)
  column_fri_proofs : (Alloc.Vec.Vec
      Plonky3_hax.Fri.FriProof
      Alloc.Alloc.Global)
  quotient_fri_proof : Plonky3_hax.Fri.FriProof
  boundary_claims : (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
  trace_log2 : u32
  ood_trace_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
  ood_trace_next_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
  ood_quotient_eval : u64
  pow_nonce : u64
  deep_fri_proof : Plonky3_hax.Fri.FriProof

--  Derive `num_layers` field-element FRI challenges per column from the
--  trace commitment. Pure function of the commitment bytes, so prover
--  and verifier produce the same vector.
def derive_fri_alphas
    (trace_commitment : (RustArray u8 32))
    (num_columns : usize)
    (num_layers : usize) :
    RustM
    (Alloc.Vec.Vec (Alloc.Vec.Vec u64 Alloc.Alloc.Global) Alloc.Alloc.Global)
    := do
  let
    result : (Alloc.Vec.Vec
      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
      Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
      num_columns);
  let
    result : (Alloc.Vec.Vec
      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
      Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_columns
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result col =>
        (do
        let row : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl.with_capacity u64 num_layers);
        let row : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            num_layers
            (fun row _ => (do (pure true) : RustM Bool))
            row
            (fun row l =>
              (do
              let acc : u64 := (0 : u64);
              let acc : u64 ←
                (Rust_primitives.Hax.Folds.fold_range
                  (0 : usize)
                  Plonky3_hax.Specs.Merkle.HASH_SIZE
                  (fun acc _ => (do (pure true) : RustM Bool))
                  acc
                  (fun acc b =>
                    (do
                    let v : u64 ←
                      (Rust_primitives.Hax.cast_op (← trace_commitment[b]_?));
                    let acc : u64 ←
                      (Plonky3_hax.Specs.Baby_bear.bb_add
                        (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
                        v);
                    (pure acc) :
                    RustM u64)));
              let acc : u64 ←
                (Plonky3_hax.Specs.Baby_bear.bb_add
                  (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
                  (← (Rust_primitives.Hax.cast_op col)));
              let acc : u64 ←
                (Plonky3_hax.Specs.Baby_bear.bb_add
                  (← (Plonky3_hax.Specs.Baby_bear.bb_mul acc (257 : u64)))
                  (← (Rust_primitives.Hax.cast_op l)));
              let row : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global row acc);
              (pure row) :
              RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
        let
          result : (Alloc.Vec.Vec
            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
            Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push
            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
            Alloc.Alloc.Global result row);
        (pure result) :
        RustM
        (Alloc.Vec.Vec
          (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
          Alloc.Alloc.Global))));
  (pure result)

--  Derive `num_queries` layer-0 query indices in `[0, n)` from the trace
--  commitment. Same deterministic-from-transcript shape as
--  `derive_fri_alphas`.
def derive_query_indices
    (trace_commitment : (RustArray u8 32))
    (num_queries : usize)
    (n : usize) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u64 num_queries);
  let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_queries
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result q =>
        (do
        let acc : u64 := (0 : u64);
        let acc : u64 ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (8 : usize)
            (fun acc _ => (do (pure true) : RustM Bool))
            acc
            (fun acc b =>
              (do
              let i : usize ←
                ((← ((← (q *? (8 : usize))) +? b))
                  %? Plonky3_hax.Specs.Merkle.HASH_SIZE);
              let acc : u64 ←
                (Rust_primitives.Hax.Machine_int.bitor
                  (← (acc <<<? (8 : i32)))
                  (← (Rust_primitives.Hax.cast_op (← trace_commitment[i]_?))));
              (pure acc) :
              RustM u64)));
        let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
            result
            (← (acc %? (← (Rust_primitives.Hax.cast_op n)))));
        (pure result) :
        RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
  (pure result)

--  The byte-wise XOR of the trace commitment, the layer-0 commitment of every
--  column FRI proof that has layers, and the quotient commitment.
def transcript_seed (proof : Plonky3Proof) : RustM (RustArray u8 32) := do
  let seed : (RustArray u8 32) := (Plonky3Proof.trace_commitment proof);
  let seed : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Alloc.Vec.Impl_1.len Plonky3_hax.Fri.FriProof Alloc.Alloc.Global
        (Plonky3Proof.column_fri_proofs proof)))
      (fun seed _ => (do (pure true) : RustM Bool))
      seed
      (fun seed i =>
        (do
        let
          layers : (Alloc.Vec.Vec
            Plonky3_hax.Fri.FriLayer
            Alloc.Alloc.Global) :=
          (Plonky3_hax.Fri.FriProof.layers
            (← (Plonky3Proof.column_fri_proofs proof)[i]_?));
        if
        (← (Core_models.Ops.Bit.Not.not
          (← (Alloc.Vec.Impl_1.is_empty
            Plonky3_hax.Fri.FriLayer
            Alloc.Alloc.Global layers)))) then
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            Plonky3_hax.Specs.Merkle.HASH_SIZE
            (fun seed _ => (do (pure true) : RustM Bool))
            seed
            (fun seed j =>
              (do
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                seed
                j
                (← ((← seed[j]_?)
                  ^^^? (← (Plonky3_hax.Fri.FriLayer.commitment
                      (← layers[(0 : usize)]_?))[
                    j
                    ]_?)))) :
              RustM (RustArray u8 32))))
        else
          (pure seed) :
        RustM (RustArray u8 32))));
  let seed : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      Plonky3_hax.Specs.Merkle.HASH_SIZE
      (fun seed _ => (do (pure true) : RustM Bool))
      seed
      (fun seed j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          seed
          j
          (← ((← seed[j]_?)
            ^^^? (← (Plonky3Proof.quotient_commitment proof)[j]_?)))) :
        RustM (RustArray u8 32))));
  (pure seed)

--  Build the row-interleaved Low-Degree Extension (LDE) of a trace on
--  the coset `shift · K`, where `K` is the multiplicative subgroup of
--  order `n = 2^domain_log2`.
-- 
--  Each column of the trace is interpreted as the evaluations of a
--  polynomial `P_col(x)` at the trace subgroup `H = {ω_h^0, ..., ω_h^{h-1}}`
--  where `h = trace.height` and `ω_h` is a primitive `h`-th root of
--  unity. The pipeline is:
-- 
--  1. `intt`: recover the coefficients of `P_col` from its evaluations
--     on `H`.
--  2. Zero-pad the coefficient vector from length `h` up to length `n`.
--  3. Coset-twist: multiply the `i`-th coefficient by `shift^i`. After
--     this, the coefficient vector represents `P(shift · x)`.
--  4. `ntt`: evaluate the twisted polynomial on `K`. By construction
--     those values are the evaluations of `P_col` on `shift · K`.
-- 
--  Use `shift = 1` to evaluate on the subgroup `K` itself (no coset).
--  The conventional Plonky3 choice is `shift = GENERATOR` so that the
--  LDE coset is disjoint from `H`.
-- 
--  The result contains `n * trace.width` values; the `i`-th block of
--  `trace.width` values is the evaluation of all columns at the `i`-th
--  domain point `shift · ω_n^i`.
-- 
--  ## Preconditions
-- 
--  - `trace.height` is a power of two.
--  - `trace.height <= 1 << domain_log2`.
--  - `domain_log2 <= 27` (Baby Bear's two-adicity).
--  - `shift` is nonzero. (Shift = 0 would collapse the entire LDE to 0.)
-- 
--  Violation of any precondition produces an empty `Vec`; callers should
--  check `compute_trace_lde(...).is_empty()` to detect the rejection.
def compute_trace_lde
    (trace : Plonky3_hax.Air.Trace)
    (domain_log2 : u32)
    (shift : u64) :
    RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global) := do
  let h : usize := (Plonky3_hax.Air.Trace.height trace);
  let n : usize ← ((1 : usize) <<<? domain_log2);
  if
  (← ((← ((← ((← ((← (Rust_primitives.Hax.Machine_int.eq h (0 : usize)))
          ||? (← (Rust_primitives.Hax.Machine_int.ne
            (← (h &&&? (← (h -? (1 : usize)))))
            (0 : usize)))))
        ||? (← (Rust_primitives.Hax.Machine_int.gt h n))))
      ||? (← (Rust_primitives.Hax.Machine_int.gt domain_log2 (27 : u32)))))
    ||? (← (Rust_primitives.Hax.Machine_int.eq shift (0 : u64))))) then
    (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk)
  else
    let trace_log2 : u32 ← (Core_models.Num.Impl_11.trailing_zeros h);
    let omega_trace : u64 ←
      (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity trace_log2);
    let omega_n : u64 ←
      (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity domain_log2);
    let result : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
      (Alloc.Vec.from_elem u64
        (0 : u64)
        (← (n *? (Plonky3_hax.Air.Trace.width trace))));
    let _ ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (Plonky3_hax.Air.Trace.width trace)
        (fun _ _ => (do (pure true) : RustM Bool))
        Rust_primitives.Hax.Tuple0.mk
        (fun _ col =>
          (do
          let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
            (Alloc.Vec.from_elem u64 (0 : u64) n);
          let coeffs : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              h
              (fun coeffs _ => (do (pure true) : RustM Bool))
              coeffs
              (fun coeffs i =>
                (do
                (Alloc.Slice.Impl.to_vec
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← (Alloc.Vec.Impl_1.as_slice coeffs))
                    i
                    (← (Plonky3_hax.Air.Impl.get trace i col))))) :
                RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
          (Rust_primitives.Hax.failure
            "The mutation of this &mut is not allowed here.

This is discussed in issue https://github.com/hacspec/hax/issues/420.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `DirectAndMut`.
"
            "{
 let Tuple2(head, _tail): tuple2<&mut [int], &mut [int]> = {
 core_models::slice::impl__split_at_mut::<
 int,
 >(&mut (deref(core_models::ops::deref::f_deref_mut(&mut (coeffs)))), h)
 };
 {
 let _: ...")
          :
          RustM Rust_primitives.Hax.Tuple0)));
    (pure result)

--  The conventional Plonky3 LDE coset shift on Baby Bear: the
--  multiplicative `GENERATOR`. Using this shift makes `shift · K`
--  disjoint from any of the trace subgroups (which all sit inside the
--  2-adic subgroup, while `GENERATOR` does not).
def LDE_COSET_SHIFT : u64 := Plonky3_hax.Specs.Baby_bear.GENERATOR

--  Commit to the interleaved LDE via a Merkle tree.
def commit_trace_lde
    (lde : (RustSlice u64))
    (width : usize)
    (domain_log2 : u32) :
    RustM (RustArray u8 32) := do
  let n : usize ← ((1 : usize) <<<? domain_log2);
  let leaves : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity (RustArray u8 32) n);
  let leaves : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      n
      (fun leaves _ => (do (pure true) : RustM Bool))
      leaves
      (fun leaves i =>
        (do
        let mixed : u64 := (0 : u64);
        let mixed : u64 ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            width
            (fun mixed _ => (do (pure true) : RustM Bool))
            mixed
            (fun mixed col =>
              (do
              (Plonky3_hax.Specs.Baby_bear.bb_add
                (← (Plonky3_hax.Specs.Baby_bear.bb_mul mixed (31 : u64)))
                (← lde[(← ((← (i *? width)) +? col))]_?)) :
              RustM u64)));
        let leaves : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push (RustArray u8 32) Alloc.Alloc.Global
            leaves
            (← (Plonky3_hax.Specs.Merkle.hash_field_elem mixed)));
        (pure leaves) :
        RustM (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global))));
  (Plonky3_hax.Specs.Merkle.merkle_build_root
    (← (Core_models.Ops.Deref.Deref.deref
      (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) leaves))
    n)

--  Default zero FRI proof: returned by `batch_fri_prove_columns`
--  when the FRI prover preconditions are violated. The caller then
--  checks `any_failed` and bails out without using the proofs.
def default_fri_proof (_ : Rust_primitives.Hax.Tuple0) :
    RustM Plonky3_hax.Fri.FriProof := do
  (pure (Plonky3_hax.Fri.FriProof.mk
    (layers := (← (Alloc.Vec.Impl.new Plonky3_hax.Fri.FriLayer
      Rust_primitives.Hax.Tuple0.mk)))
    (remainder := (Plonky3_hax.Fri.FriRemainder.mk
      (coeffs := (← (Alloc.Vec.Impl.new u64 Rust_primitives.Hax.Tuple0.mk)))))))

--  Per-column FRI: collects FriProofs and reports a separate
--  `any_failed` flag rather than threading `Option` through the loop
--  body. This keeps the early-return out of every `for` body — there
--  is no `return None` inside any loop in this function. Haxpipe
--  extracts this cleanly because the only CF marker is `cfContinue`
--  (no `cfBreak` nested under `forFoldReturn`).
def batch_fri_prove_columns
    (lde : (RustSlice u64))
    (width : usize)
    (n : usize)
    (options : Plonky3_hax.Fri.FriOptions)
    (column_alphas : (RustSlice (Alloc.Vec.Vec u64 Alloc.Alloc.Global)))
    (query_indices : (RustSlice u64)) :
    RustM
    (Rust_primitives.Hax.Tuple2
      (Alloc.Vec.Vec Plonky3_hax.Fri.FriProof Alloc.Alloc.Global)
      Bool)
    := do
  let out : (Alloc.Vec.Vec Plonky3_hax.Fri.FriProof Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity Plonky3_hax.Fri.FriProof width);
  let any_failed : Bool := false;
  let ⟨any_failed, out⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      width
      (fun ⟨any_failed, out⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk any_failed out)
      (fun ⟨any_failed, out⟩ col =>
        (do
        let vals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Alloc.Vec.from_elem u64 (0 : u64) n);
        let vals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            n
            (fun vals _ => (do (pure true) : RustM Bool))
            vals
            (fun vals i =>
              (do
              (Alloc.Slice.Impl.to_vec
                (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  (← (Alloc.Vec.Impl_1.as_slice vals))
                  i
                  (← lde[(← ((← (i *? width)) +? col))]_?)))) :
              RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
        let p : (Core_models.Option.Option Plonky3_hax.Fri.FriProof) ←
          (Plonky3_hax.Fri.fri_prove_column
            (← (Core_models.Ops.Deref.Deref.deref
              (Alloc.Vec.Vec u64 Alloc.Alloc.Global) vals))
            options
            (← (Core_models.Ops.Deref.Deref.deref
              (Alloc.Vec.Vec u64 Alloc.Alloc.Global) (← column_alphas[col]_?)))
            query_indices);
        match p with
          | (Core_models.Option.Option.Some  proof) =>
            (pure (Rust_primitives.Hax.Tuple2.mk
              any_failed
              (← (Alloc.Vec.Impl_1.push
                Plonky3_hax.Fri.FriProof
                Alloc.Alloc.Global out proof))))
          | (Core_models.Option.Option.None ) =>
            let any_failed : Bool := true;
            let
              out : (Alloc.Vec.Vec
                Plonky3_hax.Fri.FriProof
                Alloc.Alloc.Global) ←
              (Alloc.Vec.Impl_1.push Plonky3_hax.Fri.FriProof Alloc.Alloc.Global
                out
                (← (default_fri_proof Rust_primitives.Hax.Tuple0.mk)));
            (pure (Rust_primitives.Hax.Tuple2.mk any_failed out)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          Bool
          (Alloc.Vec.Vec Plonky3_hax.Fri.FriProof Alloc.Alloc.Global)))));
  (pure (Rust_primitives.Hax.Tuple2.mk out any_failed))

--  Build a proof that `trace` satisfies `air`.
-- 
--  `options` gives the FRI parameters; `options.coset_shift` is ignored and
--  `LDE_COSET_SHIFT` is used. All challenges are derived from the
--  commitments.
-- 
--  Returns `None` if the trace violates the AIR, has the wrong width, has a
--  height that is not a power of two or exceeds `2^options.domain_log2`, or
--  if an FRI or proof-of-work precondition fails.
def plonky3_prove
    (air : Plonky3_hax.Air.AirSpec)
    (trace : Plonky3_hax.Air.Trace)
    (options : Plonky3_hax.Fri.FriOptions) :
    RustM (Core_models.Option.Option Plonky3Proof) := do
  if
  (← (Rust_primitives.Hax.Machine_int.ne
    (Plonky3_hax.Air.Trace.width trace)
    (Plonky3_hax.Air.AirSpec.num_columns air))) then
    (pure Core_models.Option.Option.None)
  else
    if
    (← (Core_models.Ops.Bit.Not.not
      (← (Plonky3_hax.Air.trace_valid air trace)))) then
      (pure Core_models.Option.Option.None)
    else
      if
      (← ((← (Rust_primitives.Hax.Machine_int.eq
          (Plonky3_hax.Air.Trace.height trace)
          (0 : usize)))
        ||? (← (Rust_primitives.Hax.Machine_int.ne
          (← ((Plonky3_hax.Air.Trace.height trace)
            &&&? (← ((Plonky3_hax.Air.Trace.height trace) -? (1 : usize)))))
          (0 : usize))))) then
        (pure Core_models.Option.Option.None)
      else
        let domain_log2 : u32 :=
          (Plonky3_hax.Fri.FriOptions.domain_log2 options);
        let trace_log2 : u32 ←
          (Core_models.Num.Impl_11.trailing_zeros
            (Plonky3_hax.Air.Trace.height trace));
        if (← (Rust_primitives.Hax.Machine_int.gt trace_log2 domain_log2)) then
          (pure Core_models.Option.Option.None)
        else
          let lde : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
            (compute_trace_lde trace domain_log2 LDE_COSET_SHIFT);
          if (← (Alloc.Vec.Impl_1.is_empty u64 Alloc.Alloc.Global lde)) then
            (pure Core_models.Option.Option.None)
          else
            let trace_commitment : (RustArray u8 32) ←
              (commit_trace_lde
                (← (Core_models.Ops.Deref.Deref.deref
                  (Alloc.Vec.Vec u64 Alloc.Alloc.Global) lde))
                (Plonky3_hax.Air.Trace.width trace)
                domain_log2);
            let
              column_alphas : (Alloc.Vec.Vec
                (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                Alloc.Alloc.Global) ←
              (derive_fri_alphas
                trace_commitment
                (Plonky3_hax.Air.Trace.width trace)
                (Plonky3_hax.Fri.FriOptions.num_layers options));
            let n : usize ← ((1 : usize) <<<? domain_log2);
            let query_indices : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
              (derive_query_indices
                trace_commitment
                (Plonky3_hax.Fri.FriOptions.num_queries options)
                n);
            let column_fri_options : Plonky3_hax.Fri.FriOptions :=
              (Plonky3_hax.Fri.FriOptions.mk
                (num_layers := (Plonky3_hax.Fri.FriOptions.num_layers options))
                (domain_log2 := domain_log2)
                (num_queries := (Plonky3_hax.Fri.FriOptions.num_queries
                  options))
                (blowup := (Plonky3_hax.Fri.FriOptions.blowup options))
                (coset_shift := LDE_COSET_SHIFT)
                (proof_of_work_bits :=
                (Plonky3_hax.Fri.FriOptions.proof_of_work_bits options)));
            let ⟨proofs, any_failed⟩ ←
              (batch_fri_prove_columns
                (← (Core_models.Ops.Deref.Deref.deref
                  (Alloc.Vec.Vec u64 Alloc.Alloc.Global) lde))
                (Plonky3_hax.Air.Trace.width trace)
                n
                column_fri_options
                (← (Core_models.Ops.Deref.Deref.deref
                  (Alloc.Vec.Vec
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                    Alloc.Alloc.Global) column_alphas))
                (← (Core_models.Ops.Deref.Deref.deref
                  (Alloc.Vec.Vec u64 Alloc.Alloc.Global) query_indices)));
            if any_failed then
              (pure Core_models.Option.Option.None)
            else
              let
                column_fri_proofs : (Alloc.Vec.Vec
                  Plonky3_hax.Fri.FriProof
                  Alloc.Alloc.Global) :=
                proofs;
              let constraint_alphas : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                (Plonky3_hax.Quotient.derive_constraint_alphas
                  trace_commitment
                  (← (Alloc.Vec.Impl_1.len
                    Plonky3_hax.Air.TransitionConstraint
                    Alloc.Alloc.Global
                    (Plonky3_hax.Air.AirSpec.transitions air))));
              let quotient_lde : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                (Plonky3_hax.Quotient.compute_quotient_lde
                  (← (Core_models.Ops.Deref.Deref.deref
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global) lde))
                  air
                  (← (Core_models.Ops.Deref.Deref.deref
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global) constraint_alphas))
                  (Plonky3_hax.Air.Trace.width trace)
                  domain_log2
                  trace_log2
                  LDE_COSET_SHIFT);
              if
              (← (Alloc.Vec.Impl_1.is_empty u64 Alloc.Alloc.Global
                quotient_lde)) then
                (pure Core_models.Option.Option.None)
              else
                let quotient_commitment : (RustArray u8 32) ←
                  (Plonky3_hax.Quotient.commit_quotient_lde
                    (← (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global) quotient_lde)));
                let
                  quotient_alphas : (Alloc.Vec.Vec
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                    Alloc.Alloc.Global) ←
                  (derive_fri_alphas
                    quotient_commitment
                    (1 : usize)
                    (Plonky3_hax.Fri.FriOptions.num_layers options));
                let
                  quotient_query_indices : (Alloc.Vec.Vec
                    u64
                    Alloc.Alloc.Global) ←
                  (derive_query_indices
                    quotient_commitment
                    (Plonky3_hax.Fri.FriOptions.num_queries options)
                    n);
                let
                  quotient_fri_proof_opt : (Core_models.Option.Option
                    Plonky3_hax.Fri.FriProof) ←
                  (Plonky3_hax.Fri.fri_prove_column
                    (← (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global) quotient_lde))
                    column_fri_options
                    (← (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                      (← quotient_alphas[(0 : usize)]_?)))
                    (← (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                      quotient_query_indices)));
                match quotient_fri_proof_opt with
                  | (Core_models.Option.Option.Some  p) =>
                    let quotient_fri_proof : Plonky3_hax.Fri.FriProof := p;
                    let
                      boundary_claims : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                      (Alloc.Vec.Impl.with_capacity u64
                        (← (Alloc.Vec.Impl_1.len
                          Plonky3_hax.Air.BoundaryConstraint
                          Alloc.Alloc.Global
                          (Plonky3_hax.Air.AirSpec.boundaries air))));
                    let
                      boundary_claims : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                      (Rust_primitives.Hax.Folds.fold_range
                        (0 : usize)
                        (← (Alloc.Vec.Impl_1.len
                          Plonky3_hax.Air.BoundaryConstraint
                          Alloc.Alloc.Global
                          (Plonky3_hax.Air.AirSpec.boundaries air)))
                        (fun boundary_claims _ => (do (pure true) : RustM Bool))
                        boundary_claims
                        (fun boundary_claims k =>
                          (do
                          let b : Plonky3_hax.Air.BoundaryConstraint ←
                            (Plonky3_hax.Air.AirSpec.boundaries air)[k]_?;
                          let
                            boundary_claims : (Alloc.Vec.Vec
                              u64
                              Alloc.Alloc.Global) ←
                            (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                              boundary_claims
                              (← (Plonky3_hax.Air.Impl.get
                                trace
                                (Plonky3_hax.Air.BoundaryConstraint.row b)
                                (Plonky3_hax.Air.BoundaryConstraint.col b))));
                          (pure boundary_claims) :
                          RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
                    let z : u64 ←
                      (Plonky3_hax.Ood.derive_ood_point
                        quotient_commitment
                        trace_log2
                        domain_log2);
                    let omega_h : u64 ←
                      (Plonky3_hax.Specs.Baby_bear.bb_root_of_unity trace_log2);
                    let g_z : u64 ←
                      (Plonky3_hax.Specs.Baby_bear.bb_mul omega_h z);
                    let
                      ood_trace_evals : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                      (Plonky3_hax.Ood.evaluate_trace_at trace z);
                    let
                      ood_trace_next_evals : (Alloc.Vec.Vec
                        u64
                        Alloc.Alloc.Global) ←
                      (Plonky3_hax.Ood.evaluate_trace_at trace g_z);
                    let ood_quotient_eval : u64 ←
                      (Plonky3_hax.Ood.evaluate_quotient_at
                        (← (Core_models.Ops.Deref.Deref.deref
                          (Alloc.Vec.Vec u64 Alloc.Alloc.Global) quotient_lde))
                        domain_log2
                        LDE_COSET_SHIFT
                        z);
                    let pow_nonce_opt : (Core_models.Option.Option u64) ←
                      if
                      (← (Rust_primitives.Hax.Machine_int.eq
                        (Plonky3_hax.Fri.FriOptions.proof_of_work_bits options)
                        (0 : u32))) then
                        (pure (Core_models.Option.Option.Some (0 : u64)))
                      else
                        (Plonky3_hax.Pow.grind_pow_nonce
                          quotient_commitment
                          (Plonky3_hax.Fri.FriOptions.proof_of_work_bits
                            options)
                          (← ((1 : u64)
                            <<<? (←
                            ((Plonky3_hax.Fri.FriOptions.proof_of_work_bits
                                options)
                              +? (8 : u32))))));
                    match pow_nonce_opt with
                      | (Core_models.Option.Option.Some  n) =>
                        let pow_nonce : u64 := n;
                        let beta : u64 ←
                          (Plonky3_hax.Deep.derive_deep_beta
                            quotient_commitment);
                        let
                          all_deeps : (Alloc.Vec.Vec
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            Alloc.Alloc.Global) ←
                          (Alloc.Vec.Impl.with_capacity
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            (← ((Plonky3_hax.Air.Trace.width trace)
                              +? (1 : usize))));
                        let
                          all_deeps : (Alloc.Vec.Vec
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            Alloc.Alloc.Global) ←
                          (Rust_primitives.Hax.Folds.fold_range
                            (0 : usize)
                            (Plonky3_hax.Air.Trace.width trace)
                            (fun all_deeps _ => (do (pure true) : RustM Bool))
                            all_deeps
                            (fun all_deeps c =>
                              (do
                              let
                                p_lde : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                                (Alloc.Vec.from_elem u64 (0 : u64) n);
                              let
                                p_lde : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                                (Rust_primitives.Hax.Folds.fold_range
                                  (0 : usize)
                                  n
                                  (fun p_lde _ => (do (pure true) : RustM Bool))
                                  p_lde
                                  (fun p_lde j =>
                                    (do
                                    (Alloc.Slice.Impl.to_vec
                                      (←
                                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                        (← (Alloc.Vec.Impl_1.as_slice p_lde))
                                        j
                                        (← lde[
                                          (← ((← (j
                                              *? (Plonky3_hax.Air.Trace.width
                                                trace)))
                                            +? c))
                                          ]_?)))) :
                                    RustM
                                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
                              let
                                all_deeps : (Alloc.Vec.Vec
                                  (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                  Alloc.Alloc.Global) ←
                                (Alloc.Vec.Impl_1.push
                                  (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                  Alloc.Alloc.Global
                                  all_deeps
                                  (← (Plonky3_hax.Deep.compute_deep_poly_lde
                                    (← (Core_models.Ops.Deref.Deref.deref
                                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                      p_lde))
                                    (← ood_trace_evals[c]_?)
                                    z
                                    domain_log2
                                    LDE_COSET_SHIFT)));
                              (pure all_deeps) :
                              RustM
                              (Alloc.Vec.Vec
                                (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                Alloc.Alloc.Global))));
                        let
                          all_deeps : (Alloc.Vec.Vec
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            Alloc.Alloc.Global) ←
                          (Alloc.Vec.Impl_1.push
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            Alloc.Alloc.Global
                            all_deeps
                            (← (Plonky3_hax.Deep.compute_deep_poly_lde
                              (← (Core_models.Ops.Deref.Deref.deref
                                (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                quotient_lde))
                              ood_quotient_eval
                              z
                              domain_log2
                              LDE_COSET_SHIFT)));
                        let
                          combined_deep : (Alloc.Vec.Vec
                            u64
                            Alloc.Alloc.Global) ←
                          (Plonky3_hax.Deep.combine_deep_polys
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec
                                (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                Alloc.Alloc.Global) all_deeps))
                            beta);
                        let
                          deep_alphas : (Alloc.Vec.Vec
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            Alloc.Alloc.Global) ←
                          (derive_fri_alphas
                            quotient_commitment
                            (1 : usize)
                            (Plonky3_hax.Fri.FriOptions.num_layers options));
                        let
                          deep_fri_proof_opt : (Core_models.Option.Option
                            Plonky3_hax.Fri.FriProof) ←
                          (Plonky3_hax.Fri.fri_prove_column
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                              combined_deep))
                            column_fri_options
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                              (← deep_alphas[(0 : usize)]_?)))
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                              query_indices)));
                        match deep_fri_proof_opt with
                          | (Core_models.Option.Option.Some  p) =>
                            let deep_fri_proof : Plonky3_hax.Fri.FriProof := p;
                            (pure (Core_models.Option.Option.Some
                              (Plonky3Proof.mk
                                (trace_commitment := trace_commitment)
                                (quotient_commitment := quotient_commitment)
                                (column_fri_proofs := column_fri_proofs)
                                (quotient_fri_proof := quotient_fri_proof)
                                (boundary_claims := boundary_claims)
                                (trace_log2 := trace_log2)
                                (ood_trace_evals := ood_trace_evals)
                                (ood_trace_next_evals := ood_trace_next_evals)
                                (ood_quotient_eval := ood_quotient_eval)
                                (pow_nonce := pow_nonce)
                                (deep_fri_proof := deep_fri_proof))))
                          | (Core_models.Option.Option.None ) =>
                            (pure Core_models.Option.Option.None)
                      | (Core_models.Option.Option.None ) =>
                        (pure Core_models.Option.Option.None)
                  | (Core_models.Option.Option.None ) =>
                    (pure Core_models.Option.Option.None)

--  Verify a Plonky3 proof against an AIR specification.
-- 
--  Checks, in order:
--  1. the boundary claims agree with `air.boundaries` in number and value;
--  2. there is one FRI proof per column, and each passes `fri_verify`;
--  3. the quotient FRI proof passes `fri_verify`;
--  4. the OOD identity `C(z) = Q(z) · Z'_H(z)` holds at the re-derived `z`;
--  5. the proof-of-work nonce, when `options.proof_of_work_bits > 0`;
--  6. the DEEP FRI proof passes `fri_verify`, and its layer-0 opened values
--     equal the DEEP combination recomputed from the layer-0 openings of the
--     column and quotient proofs.
-- 
--  The folding challenges of column `col` are `column_fri_alphas[col]` when
--  that vector has at least `options.num_layers` entries, and otherwise
--  those derived from the trace commitment. The verifier does not check
--  that the query indices in the proofs are the derived ones.
def plonky3_verify
    (air : Plonky3_hax.Air.AirSpec)
    (proof : Plonky3Proof)
    (column_fri_alphas : (RustSlice (Alloc.Vec.Vec u64 Alloc.Alloc.Global)))
    (options : Plonky3_hax.Fri.FriOptions) :
    RustM Bool := do
  if
  (← (Rust_primitives.Hax.Machine_int.ne
    (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
      (Plonky3Proof.boundary_claims proof)))
    (← (Alloc.Vec.Impl_1.len
      Plonky3_hax.Air.BoundaryConstraint
      Alloc.Alloc.Global (Plonky3_hax.Air.AirSpec.boundaries air))))) then
    (pure false)
  else
    match
      (← (Rust_primitives.Hax.Folds.fold_range_return
        (0 : usize)
        (← (Alloc.Vec.Impl_1.len
          Plonky3_hax.Air.BoundaryConstraint
          Alloc.Alloc.Global (Plonky3_hax.Air.AirSpec.boundaries air)))
        (fun _ _ => (do (pure true) : RustM Bool))
        Rust_primitives.Hax.Tuple0.mk
        (fun _ k =>
          (do
          if
          (← (Rust_primitives.Hax.Machine_int.ne
            (← (Plonky3Proof.boundary_claims proof)[k]_?)
            (Plonky3_hax.Air.BoundaryConstraint.value
              (← (Plonky3_hax.Air.AirSpec.boundaries air)[k]_?)))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Core_models.Ops.Control_flow.ControlFlow.Break false)))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              Rust_primitives.Hax.Tuple0.mk)) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Core_models.Ops.Control_flow.ControlFlow
              Bool
              (Rust_primitives.Hax.Tuple2
                Rust_primitives.Hax.Tuple0
                Rust_primitives.Hax.Tuple0))
            Rust_primitives.Hax.Tuple0)))))
    with
      | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
      | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) =>
        if
        (← (Rust_primitives.Hax.Machine_int.ne
          (← (Alloc.Vec.Impl_1.len Plonky3_hax.Fri.FriProof Alloc.Alloc.Global
            (Plonky3Proof.column_fri_proofs proof)))
          (Plonky3_hax.Air.AirSpec.num_columns air))) then
          (pure false)
        else
          let
            derived_alphas : (Alloc.Vec.Vec
              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
              Alloc.Alloc.Global) ←
            (derive_fri_alphas
              (Plonky3Proof.trace_commitment proof)
              (Plonky3_hax.Air.AirSpec.num_columns air)
              (Plonky3_hax.Fri.FriOptions.num_layers options));
          let column_options : Plonky3_hax.Fri.FriOptions :=
            (Plonky3_hax.Fri.FriOptions.mk
              (num_layers := (Plonky3_hax.Fri.FriOptions.num_layers options))
              (domain_log2 := (Plonky3_hax.Fri.FriOptions.domain_log2 options))
              (num_queries := (Plonky3_hax.Fri.FriOptions.num_queries options))
              (blowup := (Plonky3_hax.Fri.FriOptions.blowup options))
              (coset_shift := (Plonky3_hax.Fri.FriOptions.coset_shift options))
              (proof_of_work_bits :=
              (Plonky3_hax.Fri.FriOptions.proof_of_work_bits options)));
          match
            (← (Rust_primitives.Hax.Folds.fold_range_return
              (0 : usize)
              (← (Alloc.Vec.Impl_1.len
                Plonky3_hax.Fri.FriProof
                Alloc.Alloc.Global (Plonky3Proof.column_fri_proofs proof)))
              (fun _ _ => (do (pure true) : RustM Bool))
              Rust_primitives.Hax.Tuple0.mk
              (fun _ col =>
                (do
                let fri_proof : Plonky3_hax.Fri.FriProof ←
                  (Plonky3Proof.column_fri_proofs proof)[col]_?;
                let alphas : (RustSlice u64) ←
                  if
                  (← ((← (Rust_primitives.Hax.Machine_int.lt
                      col
                      (← (Core_models.Slice.Impl.len
                        (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                        column_fri_alphas))))
                    &&? (← (Rust_primitives.Hax.Machine_int.ge
                      (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
                        (← column_fri_alphas[col]_?)))
                      (Plonky3_hax.Fri.FriOptions.num_layers options))))) then
                    (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                      (← column_fri_alphas[col]_?))
                  else
                    (Core_models.Ops.Deref.Deref.deref
                      (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                      (← derived_alphas[col]_?));
                if
                (← (Core_models.Ops.Bit.Not.not
                  (← (Plonky3_hax.Fri.fri_verify
                    fri_proof
                    alphas
                    column_options)))) then
                  (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                    (Core_models.Ops.Control_flow.ControlFlow.Break false)))
                else
                  (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
                    Rust_primitives.Hax.Tuple0.mk)) :
                RustM
                (Core_models.Ops.Control_flow.ControlFlow
                  (Core_models.Ops.Control_flow.ControlFlow
                    Bool
                    (Rust_primitives.Hax.Tuple2
                      Rust_primitives.Hax.Tuple0
                      Rust_primitives.Hax.Tuple0))
                  Rust_primitives.Hax.Tuple0)))))
          with
            | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) =>
              (pure ret)
            | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) =>
              let
                quotient_alphas : (Alloc.Vec.Vec
                  (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                  Alloc.Alloc.Global) ←
                (derive_fri_alphas
                  (Plonky3Proof.quotient_commitment proof)
                  (1 : usize)
                  (Plonky3_hax.Fri.FriOptions.num_layers options));
              if
              (← (Core_models.Ops.Bit.Not.not
                (← (Plonky3_hax.Fri.fri_verify
                  (Plonky3Proof.quotient_fri_proof proof)
                  (← (Core_models.Ops.Deref.Deref.deref
                    (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                    (← quotient_alphas[(0 : usize)]_?)))
                  column_options)))) then
                (pure false)
              else
                if
                (← ((← (Rust_primitives.Hax.Machine_int.ne
                    (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
                      (Plonky3Proof.ood_trace_evals proof)))
                    (Plonky3_hax.Air.AirSpec.num_columns air)))
                  ||? (← (Rust_primitives.Hax.Machine_int.ne
                    (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
                      (Plonky3Proof.ood_trace_next_evals proof)))
                    (Plonky3_hax.Air.AirSpec.num_columns air))))) then
                  (pure false)
                else
                  let z : u64 ←
                    (Plonky3_hax.Ood.derive_ood_point
                      (Plonky3Proof.quotient_commitment proof)
                      (Plonky3Proof.trace_log2 proof)
                      (Plonky3_hax.Fri.FriOptions.domain_log2 options));
                  let
                    constraint_alphas : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                    (Plonky3_hax.Quotient.derive_constraint_alphas
                      (Plonky3Proof.trace_commitment proof)
                      (← (Alloc.Vec.Impl_1.len
                        Plonky3_hax.Air.TransitionConstraint
                        Alloc.Alloc.Global
                        (Plonky3_hax.Air.AirSpec.transitions air))));
                  let c_at_z : u64 := (0 : u64);
                  let lim : usize ←
                    (Core_models.Cmp.Ord.min
                      usize
                      (← (Alloc.Vec.Impl_1.len
                        Plonky3_hax.Air.TransitionConstraint
                        Alloc.Alloc.Global
                        (Plonky3_hax.Air.AirSpec.transitions air)))
                      (← (Alloc.Vec.Impl_1.len u64 Alloc.Alloc.Global
                        constraint_alphas)));
                  let c_at_z : u64 ←
                    (Rust_primitives.Hax.Folds.fold_range
                      (0 : usize)
                      lim
                      (fun c_at_z _ => (do (pure true) : RustM Bool))
                      c_at_z
                      (fun c_at_z k =>
                        (do
                        let v : u64 ←
                          (Plonky3_hax.Air.eval_transition
                            (Plonky3_hax.Air.TransitionConstraint.kind
                              (← (Plonky3_hax.Air.AirSpec.transitions air)[
                                k
                                ]_?))
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                              (Plonky3Proof.ood_trace_evals proof)))
                            (← (Core_models.Ops.Deref.Deref.deref
                              (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                              (Plonky3Proof.ood_trace_next_evals proof))));
                        let c_at_z : u64 ←
                          (Plonky3_hax.Specs.Baby_bear.bb_add
                            c_at_z
                            (← (Plonky3_hax.Specs.Baby_bear.bb_mul
                              (← constraint_alphas[k]_?)
                              v)));
                        (pure c_at_z) :
                        RustM u64)));
                  let sel_at_z : u64 ←
                    (Plonky3_hax.Quotient.vanishing_selector_eval
                      z
                      (Plonky3Proof.trace_log2 proof));
                  let rhs : u64 ←
                    (Plonky3_hax.Specs.Baby_bear.bb_mul
                      (Plonky3Proof.ood_quotient_eval proof)
                      sel_at_z);
                  if (← (Rust_primitives.Hax.Machine_int.ne c_at_z rhs)) then
                    (pure false)
                  else
                    if
                    (← ((← (Rust_primitives.Hax.Machine_int.gt
                        (Plonky3_hax.Fri.FriOptions.proof_of_work_bits options)
                        (0 : u32)))
                      &&? (← (Core_models.Ops.Bit.Not.not
                        (← (Plonky3_hax.Pow.verify_pow_nonce
                          (Plonky3Proof.quotient_commitment proof)
                          (Plonky3Proof.pow_nonce proof)
                          (Plonky3_hax.Fri.FriOptions.proof_of_work_bits
                            options))))))) then
                      (pure false)
                    else
                      let
                        deep_alphas : (Alloc.Vec.Vec
                          (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                          Alloc.Alloc.Global) ←
                        (derive_fri_alphas
                          (Plonky3Proof.quotient_commitment proof)
                          (1 : usize)
                          (Plonky3_hax.Fri.FriOptions.num_layers options));
                      if
                      (← (Core_models.Ops.Bit.Not.not
                        (← (Plonky3_hax.Fri.fri_verify
                          (Plonky3Proof.deep_fri_proof proof)
                          (← (Core_models.Ops.Deref.Deref.deref
                            (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                            (← deep_alphas[(0 : usize)]_?)))
                          column_options)))) then
                        (pure false)
                      else
                        let beta : u64 ←
                          (Plonky3_hax.Deep.derive_deep_beta
                            (Plonky3Proof.quotient_commitment proof));
                        let claimed : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                          (Alloc.Vec.Impl.with_capacity u64
                            (← ((Plonky3_hax.Air.AirSpec.num_columns air)
                              +? (1 : usize))));
                        let claimed : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                          (Rust_primitives.Hax.Folds.fold_range
                            (0 : usize)
                            (Plonky3_hax.Air.AirSpec.num_columns air)
                            (fun claimed _ => (do (pure true) : RustM Bool))
                            claimed
                            (fun claimed c =>
                              (do
                              (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                                claimed
                                (← (Plonky3Proof.ood_trace_evals proof)[c]_?)) :
                              RustM (Alloc.Vec.Vec u64 Alloc.Alloc.Global))));
                        let claimed : (Alloc.Vec.Vec u64 Alloc.Alloc.Global) ←
                          (Alloc.Vec.Impl_1.push u64 Alloc.Alloc.Global
                            claimed
                            (Plonky3Proof.ood_quotient_eval proof));
                        let
                          deep_queries : (Alloc.Vec.Vec
                            Plonky3_hax.Fri.FriLayerQuery
                            Alloc.Alloc.Global) :=
                          (Plonky3_hax.Fri.FriLayer.queries
                            (← (Plonky3_hax.Fri.FriProof.layers
                                (Plonky3Proof.deep_fri_proof proof))[
                              (0 : usize)
                              ]_?));
                        match
                          (← (Rust_primitives.Hax.Folds.fold_range_return
                            (0 : usize)
                            (← (Alloc.Vec.Impl_1.len
                              Plonky3_hax.Fri.FriLayerQuery
                              Alloc.Alloc.Global deep_queries))
                            (fun _ _ => (do (pure true) : RustM Bool))
                            Rust_primitives.Hax.Tuple0.mk
                            (fun _ q =>
                              (do
                              let dq : Plonky3_hax.Fri.FriLayerQuery ←
                                deep_queries[q]_?;
                              let x_q : u64 ←
                                (Plonky3_hax.Fri.coset_element
                                  (Plonky3_hax.Fri.FriOptions.coset_shift
                                    options)
                                  (Plonky3_hax.Fri.FriOptions.domain_log2
                                    options)
                                  (Plonky3_hax.Fri.FriLayerQuery.index_pos dq));
                              let
                                p_openings : (Alloc.Vec.Vec
                                  u64
                                  Alloc.Alloc.Global) ←
                                (Alloc.Vec.Impl.with_capacity u64
                                  (← ((Plonky3_hax.Air.AirSpec.num_columns air)
                                    +? (1 : usize))));
                              match
                                (← (Rust_primitives.Hax.Folds.fold_range_return
                                  (0 : usize)
                                  (Plonky3_hax.Air.AirSpec.num_columns air)
                                  (fun p_openings _ =>
                                    (do (pure true) : RustM Bool))
                                  p_openings
                                  (fun p_openings c2 =>
                                    (do
                                    if
                                    (← ((← (Alloc.Vec.Impl_1.is_empty
                                        Plonky3_hax.Fri.FriLayer
                                        Alloc.Alloc.Global
                                        (Plonky3_hax.Fri.FriProof.layers
                                          (← (Plonky3Proof.column_fri_proofs
                                              proof)[
                                            c2
                                            ]_?))))
                                      ||? (← (Rust_primitives.Hax.Machine_int.ge
                                        q
                                        (← (Alloc.Vec.Impl_1.len
                                          Plonky3_hax.Fri.FriLayerQuery
                                          Alloc.Alloc.Global
                                          (Plonky3_hax.Fri.FriLayer.queries
                                            (← (Plonky3_hax.Fri.FriProof.layers
                                                (←
                                                (Plonky3Proof.column_fri_proofs
                                                    proof)[
                                                  c2
                                                  ]_?))[
                                              (0 : usize)
                                              ]_?)))))))) then
                                      (pure
                                      (Core_models.Ops.Control_flow.ControlFlow.Break
                                        (Core_models.Ops.Control_flow.ControlFlow.Break
                                          false)))
                                    else
                                      (pure
                                      (Core_models.Ops.Control_flow.ControlFlow.Continue
                                        (← (Alloc.Vec.Impl_1.push
                                          u64
                                          Alloc.Alloc.Global
                                          p_openings
                                          (Plonky3_hax.Fri.FriLayerQuery.eval_pos
                                            (← (Plonky3_hax.Fri.FriLayer.queries
                                                (←
                                                (Plonky3_hax.Fri.FriProof.layers
                                                    (←
                                                    (Plonky3Proof.column_fri_proofs
                                                        proof)[
                                                      c2
                                                      ]_?))[
                                                  (0 : usize)
                                                  ]_?))[
                                              q
                                              ]_?)))))) :
                                    RustM
                                    (Core_models.Ops.Control_flow.ControlFlow
                                      (Core_models.Ops.Control_flow.ControlFlow
                                        Bool
                                        (Rust_primitives.Hax.Tuple2
                                          Rust_primitives.Hax.Tuple0
                                          (Alloc.Vec.Vec
                                            u64
                                            Alloc.Alloc.Global)))
                                      (Alloc.Vec.Vec
                                        u64
                                        Alloc.Alloc.Global))))))
                              with
                                |
                                  (Core_models.Ops.Control_flow.ControlFlow.Break
                                     ret) =>
                                  (pure
                                  (Core_models.Ops.Control_flow.ControlFlow.Break
                                    (Core_models.Ops.Control_flow.ControlFlow.Break
                                      ret)))
                                |
                                  (Core_models.Ops.Control_flow.ControlFlow.Continue
                                     p_openings) =>
                                  if
                                  (← ((← (Alloc.Vec.Impl_1.is_empty
                                      Plonky3_hax.Fri.FriLayer
                                      Alloc.Alloc.Global
                                      (Plonky3_hax.Fri.FriProof.layers
                                        (Plonky3Proof.quotient_fri_proof
                                          proof))))
                                    ||? (← (Rust_primitives.Hax.Machine_int.ge
                                      q
                                      (← (Alloc.Vec.Impl_1.len
                                        Plonky3_hax.Fri.FriLayerQuery
                                        Alloc.Alloc.Global
                                        (Plonky3_hax.Fri.FriLayer.queries
                                          (← (Plonky3_hax.Fri.FriProof.layers
                                              (Plonky3Proof.quotient_fri_proof
                                                proof))[
                                            (0 : usize)
                                            ]_?)))))))) then
                                    (pure
                                    (Core_models.Ops.Control_flow.ControlFlow.Break
                                      (Core_models.Ops.Control_flow.ControlFlow.Break
                                        false)))
                                  else
                                    let
                                      p_openings : (Alloc.Vec.Vec
                                        u64
                                        Alloc.Alloc.Global) ←
                                      (Alloc.Vec.Impl_1.push
                                        u64
                                        Alloc.Alloc.Global
                                        p_openings
                                        (Plonky3_hax.Fri.FriLayerQuery.eval_pos
                                          (← (Plonky3_hax.Fri.FriLayer.queries
                                              (←
                                              (Plonky3_hax.Fri.FriProof.layers
                                                  (Plonky3Proof.quotient_fri_proof
                                                    proof))[
                                                (0 : usize)
                                                ]_?))[
                                            q
                                            ]_?)));
                                    let reconstructed : u64 ←
                                      (Plonky3_hax.Deep.reconstruct_deep_value_at
                                        (← (Core_models.Ops.Deref.Deref.deref
                                          (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                          p_openings))
                                        (← (Core_models.Ops.Deref.Deref.deref
                                          (Alloc.Vec.Vec u64 Alloc.Alloc.Global)
                                          claimed))
                                        x_q
                                        z
                                        beta);
                                    if
                                    (← (Rust_primitives.Hax.Machine_int.ne
                                      (Plonky3_hax.Fri.FriLayerQuery.eval_pos
                                        dq)
                                      reconstructed)) then
                                      (pure
                                      (Core_models.Ops.Control_flow.ControlFlow.Break
                                        (Core_models.Ops.Control_flow.ControlFlow.Break
                                          false)))
                                    else
                                      (pure
                                      (Core_models.Ops.Control_flow.ControlFlow.Continue
                                        Rust_primitives.Hax.Tuple0.mk)) :
                              RustM
                              (Core_models.Ops.Control_flow.ControlFlow
                                (Core_models.Ops.Control_flow.ControlFlow
                                  Bool
                                  (Rust_primitives.Hax.Tuple2
                                    Rust_primitives.Hax.Tuple0
                                    Rust_primitives.Hax.Tuple0))
                                Rust_primitives.Hax.Tuple0)))))
                        with
                          | (Core_models.Ops.Control_flow.ControlFlow.Break
                               ret) =>
                            (pure ret)
                          | (Core_models.Ops.Control_flow.ControlFlow.Continue
                               _) =>
                            (pure true)

end Plonky3_hax.Plonky3


namespace Plonky3_hax

--  A Baby Bear field element: a `u64` in `[0, BABY_BEAR_PRIME)`.
abbrev P3Field : Type := u64

--  Merkle root commitment (32 bytes).
abbrev P3Commitment : Type := (RustArray u8 32)

--  A 256-byte opening proof for `p3_verify_opening`.
abbrev P3Proof : Type := (RustArray u8 256)

--  Field arithmetic and hashing used by the STARK.
-- 
--  `BabyBearPlonky3` instantiates it with `specs::baby_bear` and the
--  `specs::merkle` hash.
class Plonky3Crypto.AssociatedTypes (Self : Type) where

class Plonky3Crypto (Self : Type)
  [associatedTypes : outParam (Plonky3Crypto.AssociatedTypes (Self : Type))]
  where
  field_add (Self) : (u64 -> u64 -> RustM u64)
  field_mul (Self) : (u64 -> u64 -> RustM u64)
  field_inv (Self) : (u64 -> RustM u64)
  hash_compress (Self) :
    ((RustArray u8 32) -> (RustArray u8 32) -> RustM (RustArray u8 32))
  merkle_commit (Self) : ((RustSlice u64) -> RustM (RustArray u8 32))

--  Default Baby Bear instantiation of `Plonky3Crypto`.
structure BabyBearPlonky3 where
  -- no fields

@[reducible] instance Impl.AssociatedTypes :
  Plonky3Crypto.AssociatedTypes BabyBearPlonky3
  where

instance Impl : Plonky3Crypto BabyBearPlonky3 where
  field_add := fun (a : u64) (b : u64) => do
    (Plonky3_hax.Specs.Baby_bear.bb_add a b)
  field_mul := fun (a : u64) (b : u64) => do
    (Plonky3_hax.Specs.Baby_bear.bb_mul a b)
  field_inv := fun (a : u64) => do (Plonky3_hax.Specs.Baby_bear.bb_inv a)
  hash_compress :=
    fun (left : (RustArray u8 32)) (right : (RustArray u8 32)) => do
    (Plonky3_hax.Specs.Merkle.hash_two_to_one left right)
  merkle_commit := fun (data : (RustSlice u64)) => do
    let hashes : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
      (Alloc.Vec.Impl.with_capacity (RustArray u8 32)
        (← (Core_models.Slice.Impl.len u64 data)));
    let hashes : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (← (Core_models.Slice.Impl.len u64 data))
        (fun hashes _ => (do (pure true) : RustM Bool))
        hashes
        (fun hashes i =>
          (do
          (Alloc.Vec.Impl_1.push (RustArray u8 32) Alloc.Alloc.Global
            hashes
            (← (Plonky3_hax.Specs.Merkle.hash_field_elem (← data[i]_?)))) :
          RustM (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global))));
    let n : usize := (1 : usize);
    let n : usize ←
      (Rust_primitives.Hax.Folds.fold_range_cf
        (0 : usize)
        (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_11.BITS))
        (fun n _ => (do (pure true) : RustM Bool))
        n
        (fun n _ =>
          (do
          if
          (← (Rust_primitives.Hax.Machine_int.ge
            n
            (← (Core_models.Slice.Impl.len u64 data)))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Rust_primitives.Hax.Tuple2.mk Rust_primitives.Hax.Tuple0.mk n)))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (← (n <<<? (1 : i32))))) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 usize)
            usize))));
    let pad_to : usize := n;
    let cur : usize ←
      (Alloc.Vec.Impl_1.len (RustArray u8 32) Alloc.Alloc.Global hashes);
    let hashes : (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) ←
      (Rust_primitives.Hax.Folds.fold_range
        cur
        pad_to
        (fun hashes _ => (do (pure true) : RustM Bool))
        hashes
        (fun hashes _ =>
          (do
          (Alloc.Vec.Impl_1.push (RustArray u8 32) Alloc.Alloc.Global
            hashes
            (← (Rust_primitives.Hax.repeat (0 : u8) (32 : usize)))) :
          RustM (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global))));
    (Plonky3_hax.Specs.Merkle.merkle_build_root
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec (RustArray u8 32) Alloc.Alloc.Global) hashes))
      n)

--  FRI folding step at the point `x = 1`: `fri::fri_fold(f_pos, f_neg, 1, alpha)`.
def p3_fold (f_pos : u64) (f_neg : u64) (alpha : u64) : RustM u64 := do
  (Plonky3_hax.Fri.fri_fold f_pos f_neg (1 : u64) alpha)

--  Constraint verification: succeeds iff the evaluation equals the
--  expected value.
def p3_verify_constraint (c_eval : u64) (expected : u64) : RustM Bool := do
  (Rust_primitives.Hax.Machine_int.eq c_eval expected)

--  Returns `true` iff the first 32 bytes of `proof` equal `commitment`.
-- 
--  The point and the claimed evaluation are not checked; this function is
--  not an opening verifier. Openings of the STARK are checked by
--  [`fri::fri_verify`] and [`specs::merkle::merkle_verify_path`].
def p3_verify_opening
    (commitment : (RustArray u8 32))
    (_point : u64)
    (_claimed_eval : u64)
    (proof : (RustArray u8 256)) :
    RustM Bool := do
  match
    (← (Rust_primitives.Hax.Folds.fold_range_return
      (0 : usize)
      (32 : usize)
      (fun _ _ => (do (pure true) : RustM Bool))
      Rust_primitives.Hax.Tuple0.mk
      (fun _ i =>
        (do
        if
        (← (Rust_primitives.Hax.Machine_int.ne
          (← proof[i]_?)
          (← commitment[i]_?))) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Core_models.Ops.Control_flow.ControlFlow.Break false)))
        else
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            Rust_primitives.Hax.Tuple0.mk)) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Core_models.Ops.Control_flow.ControlFlow
            Bool
            (Rust_primitives.Hax.Tuple2
              Rust_primitives.Hax.Tuple0
              Rust_primitives.Hax.Tuple0))
          Rust_primitives.Hax.Tuple0)))))
  with
    | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
    | (Core_models.Ops.Control_flow.ControlFlow.Continue  _) => (pure true)

end Plonky3_hax

