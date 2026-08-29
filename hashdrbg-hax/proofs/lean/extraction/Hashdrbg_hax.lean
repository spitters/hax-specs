
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


namespace Hashdrbg_hax

--  SHA-256 initial hash values (FIPS 180-4, Section 5.3.3).
def SHA256_H0 : (RustArray u32 8) :=
  RustM.of_isOk
    (do
    #v[(1779033703 : u32),
         (3144134277 : u32),
         (1013904242 : u32),
         (2773480762 : u32),
         (1359893119 : u32),
         (2600822924 : u32),
         (528734635 : u32),
         (1541459225 : u32)])
    (by rfl)

--  SHA-256 round constants (FIPS 180-4, Section 4.2.2).
def SHA256_K : (RustArray u32 64) :=
  RustM.of_isOk
    (do
    #v[(1116352408 : u32),
         (1899447441 : u32),
         (3049323471 : u32),
         (3921009573 : u32),
         (961987163 : u32),
         (1508970993 : u32),
         (2453635748 : u32),
         (2870763221 : u32),
         (3624381080 : u32),
         (310598401 : u32),
         (607225278 : u32),
         (1426881987 : u32),
         (1925078388 : u32),
         (2162078206 : u32),
         (2614888103 : u32),
         (3248222580 : u32),
         (3835390401 : u32),
         (4022224774 : u32),
         (264347078 : u32),
         (604807628 : u32),
         (770255983 : u32),
         (1249150122 : u32),
         (1555081692 : u32),
         (1996064986 : u32),
         (2554220882 : u32),
         (2821834349 : u32),
         (2952996808 : u32),
         (3210313671 : u32),
         (3336571891 : u32),
         (3584528711 : u32),
         (113926993 : u32),
         (338241895 : u32),
         (666307205 : u32),
         (773529912 : u32),
         (1294757372 : u32),
         (1396182291 : u32),
         (1695183700 : u32),
         (1986661051 : u32),
         (2177026350 : u32),
         (2456956037 : u32),
         (2730485921 : u32),
         (2820302411 : u32),
         (3259730800 : u32),
         (3345764771 : u32),
         (3516065817 : u32),
         (3600352804 : u32),
         (4094571909 : u32),
         (275423344 : u32),
         (430227734 : u32),
         (506948616 : u32),
         (659060556 : u32),
         (883997877 : u32),
         (958139571 : u32),
         (1322822218 : u32),
         (1537002063 : u32),
         (1747873779 : u32),
         (1955562222 : u32),
         (2024104815 : u32),
         (2227730452 : u32),
         (2361852424 : u32),
         (2428436474 : u32),
         (2756734187 : u32),
         (3204031479 : u32),
         (3329325298 : u32)])
    (by rfl)

--  SHA-256 block size in bytes.
def SHA256_BLOCK_SIZE : usize := (64 : usize)

--  SHA-256 digest size in bytes (outlen for Hash_DRBG).
def SHA256_DIGEST_SIZE : usize := (32 : usize)

--  SHA-256 state.
structure Sha256State where
  h : (RustArray u32 8)
  buf : (RustArray u8 64)
  buf_len : usize
  total_len : u64

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes Sha256State :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Clone.Clone Sha256State :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes Sha256State :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  Core_models.Marker.Copy Sha256State :=
  by constructor <;> exact Inhabited.default

--  Maximum input length for sha256_update (for hax bounded iteration).
--  Hash_DRBG needs to hash at most: 1 + 55 + MAX_PERSONALIZATION = 1 + 55 + 256 = 312 bytes.
--  We set this generously to cover all internal uses.
def MAX_HASH_INPUT_LEN : usize := (512 : usize)

--  Initialize SHA-256 state.
def Impl.new (_ : Rust_primitives.Hax.Tuple0) : RustM Sha256State := do
  (pure (Sha256State.mk
    (h := SHA256_H0)
    (buf := (← (Rust_primitives.Hax.repeat (0 : u8) (64 : usize))))
    (buf_len := (0 : usize))
    (total_len := (0 : u64))))

def ch (x : u32) (y : u32) (z : u32) : RustM u32 := do
  ((← (x &&&? y)) ^^^? (← ((← (Rust_primitives.Hax.Machine_int.not x)) &&&? z)))

def maj (x : u32) (y : u32) (z : u32) : RustM u32 := do
  ((← ((← (x &&&? y)) ^^^? (← (x &&&? z)))) ^^^? (← (y &&&? z)))

def sigma0 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (2 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (13 : u32)))))
    ^^^? (← (Core_models.Num.Impl_8.rotate_right x (22 : u32))))

def sigma1 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (6 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (11 : u32)))))
    ^^^? (← (Core_models.Num.Impl_8.rotate_right x (25 : u32))))

def lsigma0 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (7 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (18 : u32)))))
    ^^^? (← (x >>>? (3 : i32))))

def lsigma1 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (17 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (19 : u32)))))
    ^^^? (← (x >>>? (10 : i32))))

--  Process a single 64-byte block (SHA-256 compression function).
def sha256_compress (state : (RustArray u32 8)) (block : (RustArray u8 64)) :
    RustM (RustArray u32 8) := do
  let w : (RustArray u32 64) ←
    (Rust_primitives.Hax.repeat (0 : u32) (64 : usize));
  let w : (RustArray u32 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun w _ => (do (pure true) : RustM Bool))
      w
      (fun w i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          w
          i
          (← (Rust_primitives.Hax.Machine_int.bitor
            (← (Rust_primitives.Hax.Machine_int.bitor
              (← (Rust_primitives.Hax.Machine_int.bitor
                (← ((← (Rust_primitives.Hax.cast_op
                    (← block[(← (i *? (4 : usize)))]_?)))
                  <<<? (24 : i32)))
                (← ((← (Rust_primitives.Hax.cast_op
                    (← block[(← ((← (i *? (4 : usize))) +? (1 : usize)))]_?)))
                  <<<? (16 : i32)))))
              (← ((← (Rust_primitives.Hax.cast_op
                  (← block[(← ((← (i *? (4 : usize))) +? (2 : usize)))]_?)))
                <<<? (8 : i32)))))
            (← (Rust_primitives.Hax.cast_op
              (← block[(← ((← (i *? (4 : usize))) +? (3 : usize)))]_?)))))) :
        RustM (RustArray u32 64))));
  let w : (RustArray u32 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (16 : usize)
      (64 : usize)
      (fun w _ => (do (pure true) : RustM Bool))
      w
      (fun w i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          w
          i
          (← (Core_models.Num.Impl_8.wrapping_add
            (← (Core_models.Num.Impl_8.wrapping_add
              (← (Core_models.Num.Impl_8.wrapping_add
                (← (lsigma1 (← w[(← (i -? (2 : usize)))]_?)))
                (← w[(← (i -? (7 : usize)))]_?)))
              (← (lsigma0 (← w[(← (i -? (15 : usize)))]_?)))))
            (← w[(← (i -? (16 : usize)))]_?)))) :
        RustM (RustArray u32 64))));
  let a : u32 ← state[(0 : usize)]_?;
  let b : u32 ← state[(1 : usize)]_?;
  let c : u32 ← state[(2 : usize)]_?;
  let d : u32 ← state[(3 : usize)]_?;
  let e : u32 ← state[(4 : usize)]_?;
  let f : u32 ← state[(5 : usize)]_?;
  let g : u32 ← state[(6 : usize)]_?;
  let h : u32 ← state[(7 : usize)]_?;
  let ⟨a, b, c, d, e, f, g, h⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (64 : usize)
      (fun ⟨a, b, c, d, e, f, g, h⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple8.mk a b c d e f g h)
      (fun ⟨a, b, c, d, e, f, g, h⟩ i =>
        (do
        let t1 : u32 ←
          (Core_models.Num.Impl_8.wrapping_add
            (← (Core_models.Num.Impl_8.wrapping_add
              (← (Core_models.Num.Impl_8.wrapping_add
                (← (Core_models.Num.Impl_8.wrapping_add h (← (sigma1 e))))
                (← (ch e f g))))
              (← SHA256_K[i]_?)))
            (← w[i]_?));
        let t2 : u32 ←
          (Core_models.Num.Impl_8.wrapping_add (← (sigma0 a)) (← (maj a b c)));
        let h : u32 := g;
        let g : u32 := f;
        let f : u32 := e;
        let e : u32 ← (Core_models.Num.Impl_8.wrapping_add d t1);
        let d : u32 := c;
        let c : u32 := b;
        let b : u32 := a;
        let a : u32 ← (Core_models.Num.Impl_8.wrapping_add t1 t2);
        (pure (Rust_primitives.Hax.Tuple8.mk a b c d e f g h)) :
        RustM (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32))));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (0 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(0 : usize)]_?) a)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (1 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(1 : usize)]_?) b)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (2 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(2 : usize)]_?) c)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (3 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(3 : usize)]_?) d)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (4 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(4 : usize)]_?) e)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (5 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(5 : usize)]_?) f)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (6 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(6 : usize)]_?) g)));
  let state : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (7 : usize)
      (← (Core_models.Num.Impl_8.wrapping_add (← state[(7 : usize)]_?) h)));
  (pure state)

--  Update SHA-256 state with data.
def sha256_update
    (state : Sha256State)
    (data : (RustSlice u8))
    (data_len : usize) :
    RustM Sha256State := do
  let processed : usize := (0 : usize);
  let ⟨processed, state⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      (← ((← ((← (MAX_HASH_INPUT_LEN +? (← (SHA256_BLOCK_SIZE *? (2 : usize)))))
          /? SHA256_BLOCK_SIZE))
        +? (2 : usize)))
      (fun ⟨processed, state⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk processed state)
      (fun ⟨processed, state⟩ _iter =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge processed data_len)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk processed state))))
        else
          let remaining : usize ← (data_len -? processed);
          let space : usize ←
            (SHA256_BLOCK_SIZE -? (Sha256State.buf_len state));
          let to_copy : usize ←
            if (← (Rust_primitives.Hax.Machine_int.lt remaining space)) then
              (pure remaining)
            else
              (pure space);
          let state : Sha256State ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              to_copy
              (fun state _ => (do (pure true) : RustM Bool))
              state
              (fun state i =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← (processed +? i))
                  data_len)) then
                  let state : Sha256State :=
                    {state
                    with buf := (←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      (Sha256State.buf state)
                      (← ((Sha256State.buf_len state) +? i))
                      (← data[(← (processed +? i))]_?)))};
                  (pure state)
                else
                  (pure state) :
                RustM Sha256State)));
          let state : Sha256State :=
            {state
            with buf_len := (← ((Sha256State.buf_len state) +? to_copy))};
          let processed : usize ← (processed +? to_copy);
          let state : Sha256State :=
            {state
            with total_len := (← (Core_models.Num.Impl_9.wrapping_add
              (Sha256State.total_len state)
              (← (Rust_primitives.Hax.cast_op to_copy))))};
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (Sha256State.buf_len state)
            SHA256_BLOCK_SIZE)) then
            let block : (RustArray u8 64) := (Sha256State.buf state);
            let state : Sha256State :=
              {state
              with h := (← (sha256_compress (Sha256State.h state) block))};
            let state : Sha256State := {state with buf_len := (0 : usize)};
            let state : Sha256State :=
              {state
              with buf := (← (Rust_primitives.Hax.repeat
                (0 : u8)
                (64 : usize)))};
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (Rust_primitives.Hax.Tuple2.mk processed state)))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (Rust_primitives.Hax.Tuple2.mk processed state))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2 usize Sha256State))
          (Rust_primitives.Hax.Tuple2 usize Sha256State)))));
  (pure state)

--  Finalize SHA-256 and produce 32-byte digest.
def sha256_finalize (state : Sha256State) : RustM (RustArray u8 32) := do
  let bit_len : u64 ←
    (Core_models.Num.Impl_9.wrapping_mul
      (Sha256State.total_len state)
      (8 : u64));
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (Sha256State.buf_len state)
      (128 : u8)))};
  let state : Sha256State :=
    {state with buf_len := (← ((Sha256State.buf_len state) +? (1 : usize)))};
  let state : Sha256State ←
    if
    (← (Rust_primitives.Hax.Machine_int.gt
      (Sha256State.buf_len state)
      (56 : usize))) then
      let state : Sha256State ←
        (Rust_primitives.Hax.Folds.fold_range
          (Sha256State.buf_len state)
          (64 : usize)
          (fun state _ => (do (pure true) : RustM Bool))
          state
          (fun state i =>
            (do
            (pure {state
            with buf := (←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (Sha256State.buf state)
              i
              (0 : u8)))}) :
            RustM Sha256State)));
      let block : (RustArray u8 64) := (Sha256State.buf state);
      let state : Sha256State :=
        {state with h := (← (sha256_compress (Sha256State.h state) block))};
      let state : Sha256State :=
        {state
        with buf := (← (Rust_primitives.Hax.repeat (0 : u8) (64 : usize)))};
      let state : Sha256State := {state with buf_len := (0 : usize)};
      (pure state)
    else
      (pure state);
  let state : Sha256State ←
    (Rust_primitives.Hax.Folds.fold_range
      (Sha256State.buf_len state)
      (56 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (pure {state
        with buf := (←
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          (Sha256State.buf state)
          i
          (0 : u8)))}) :
        RustM Sha256State)));
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (56 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (56 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (57 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (48 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (58 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (40 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (59 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (32 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (60 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (24 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (61 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (16 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (62 : usize)
      (← (Rust_primitives.Hax.cast_op (← (bit_len >>>? (8 : i32)))))))};
  let state : Sha256State :=
    {state
    with buf := (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      (Sha256State.buf state)
      (63 : usize)
      (← (Rust_primitives.Hax.cast_op bit_len))))};
  let block : (RustArray u8 64) := (Sha256State.buf state);
  let state : Sha256State :=
    {state with h := (← (sha256_compress (Sha256State.h state) block))};
  let digest : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let digest : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun digest _ => (do (pure true) : RustM Bool))
      digest
      (fun digest i =>
        (do
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← (i *? (4 : usize)))
            (← (Rust_primitives.Hax.cast_op
              (← ((← (Sha256State.h state)[i]_?) >>>? (24 : i32))))));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((← (i *? (4 : usize))) +? (1 : usize)))
            (← (Rust_primitives.Hax.cast_op
              (← ((← (Sha256State.h state)[i]_?) >>>? (16 : i32))))));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((← (i *? (4 : usize))) +? (2 : usize)))
            (← (Rust_primitives.Hax.cast_op
              (← ((← (Sha256State.h state)[i]_?) >>>? (8 : i32))))));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((← (i *? (4 : usize))) +? (3 : usize)))
            (← (Rust_primitives.Hax.cast_op (← (Sha256State.h state)[i]_?))));
        (pure digest) :
        RustM (RustArray u8 32))));
  (pure digest)

--  SHA-256 one-shot: hash `data[0..data_len]`.
def sha256 (data : (RustSlice u8)) (data_len : usize) :
    RustM (RustArray u8 32) := do
  let state : Sha256State ← (Impl.new Rust_primitives.Hax.Tuple0.mk);
  let state : Sha256State ← (sha256_update state data data_len);
  (sha256_finalize state)

--  seedlen for SHA-256: 440 bits = 55 bytes.
def SEEDLEN : usize := (55 : usize)

--  outlen for SHA-256: 256 bits = 32 bytes.
def OUTLEN : usize := SHA256_DIGEST_SIZE

--  Maximum output bytes per generate call: 128 bytes (4 SHA-256 blocks).
--  This is well within the SP 800-90A limit of 2^19 bits.
def MAX_OUTPUT : usize := (128 : usize)

--  Maximum number of hash iterations in hashgen: ceil(MAX_OUTPUT * 8 / 256) = 4.
def MAX_HASHGEN_ITERS : usize :=
  RustM.of_isOk
    (do ((← ((← (MAX_OUTPUT +? OUTLEN)) -? (1 : usize))) /? OUTLEN))
    (by rfl)

--  Maximum personalization string length (bytes).
def MAX_PERSONALIZATION_LEN : usize := (256 : usize)

--  Maximum additional input length (bytes).
def MAX_ADDITIONAL_INPUT_LEN : usize := (256 : usize)

--  Maximum entropy + nonce + personalization for seed_material buffer.
--  entropy(55) + nonce(32) + personalization(256) = 343 bytes.
def MAX_SEED_MATERIAL_LEN : usize := (384 : usize)

--  Maximum input to Hash_df: 1(counter) + 4(num_bits) + seed_material.
--  For the 0x00||V case: 1 + 55 = 56.
--  For seed_material case: 1 + 4 + 384 = 389.
def MAX_HASH_DF_INPUT_LEN : usize := (400 : usize)

--  Maximum number of Hash_df hash iterations: ceil(55 / 32) = 2.
def MAX_HASH_DF_ITERS : usize :=
  RustM.of_isOk
    (do ((← ((← (SEEDLEN +? OUTLEN)) -? (1 : usize))) /? OUTLEN))
    (by rfl)

--  Hash_DRBG internal state (SP 800-90A, Section 10.1.1).
-- 
--  V and C are seedlen-byte values. reseed_counter tracks usage.
structure HashDrbgState where
  v : (RustArray u8 55)
  c : (RustArray u8 55)
  reseed_counter : u64

@[instance] opaque Impl_4.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes HashDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  Core_models.Clone.Clone HashDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes HashDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  Core_models.Marker.Copy HashDrbgState :=
  by constructor <;> exact Inhabited.default

--  Create a zeroed (uninitialized) state.
def Impl_1.new (_ : Rust_primitives.Hax.Tuple0) : RustM HashDrbgState := do
  (pure (HashDrbgState.mk
    (v := (← (Rust_primitives.Hax.repeat (0 : u8) (55 : usize))))
    (c := (← (Rust_primitives.Hax.repeat (0 : u8) (55 : usize))))
    (reseed_counter := (0 : u64))))

--  Add two seedlen-byte big-endian numbers modulo 2^(seedlen*8).
-- 
--  Performs byte-by-byte addition from LSB (index SEEDLEN-1) to MSB (index 0),
--  with carry propagation. Any carry out of the MSB is discarded (mod 2^seedlen).
def add_mod_seedlen (a : (RustArray u8 55)) (b : (RustArray u8 55)) :
    RustM (RustArray u8 55) := do
  let result : (RustArray u8 55) ←
    (Rust_primitives.Hax.repeat (0 : u8) (55 : usize));
  let carry : u16 := (0 : u16);
  let ⟨carry, result⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun ⟨carry, result⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk carry result)
      (fun ⟨carry, result⟩ j =>
        (do
        let i : usize ← ((← (SEEDLEN -? (1 : usize))) -? j);
        let sum : u16 ←
          ((← ((← (Rust_primitives.Hax.cast_op (← a[i]_?)))
              +? (← (Rust_primitives.Hax.cast_op (← b[i]_?)))))
            +? carry);
        let result : (RustArray u8 55) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← (Rust_primitives.Hax.cast_op sum)));
        let carry : u16 ← (sum >>>? (8 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk carry result)) :
        RustM (Rust_primitives.Hax.Tuple2 u16 (RustArray u8 55)))));
  (pure result)

--  Add a u64 value to a seedlen-byte big-endian number modulo 2^(seedlen*8).
-- 
--  The u64 is treated as an 8-byte big-endian value added to the least
--  significant bytes.
def add_u64_mod_seedlen (a : (RustArray u8 55)) (val : u64) :
    RustM (RustArray u8 55) := do
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.repeat (0 : u8) (55 : usize));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (8 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (56 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (7 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (48 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (6 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (40 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (5 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (32 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (4 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (24 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (3 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (16 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (2 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (val >>>? (8 : i32))))));
  let b : (RustArray u8 55) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b
      (← (SEEDLEN -? (1 : usize)))
      (← (Rust_primitives.Hax.cast_op val)));
  (add_mod_seedlen a b)

--  Increment a seedlen-byte big-endian number by 1 modulo 2^(seedlen*8).
def increment_mod_seedlen (a : (RustArray u8 55)) :
    RustM (RustArray u8 55) := do
  (add_u64_mod_seedlen a (1 : u64))

--  Hash_df: Hash Derivation Function (SP 800-90A, Section 10.3.1).
-- 
--  Derives `num_bits / 8` bytes from `input[0..input_len]`.
--  For Hash_DRBG with SHA-256, num_bits is always 440 (seedlen in bits).
-- 
--  Algorithm:
--    counter = 1
--    temp = empty
--    while len(temp) < num_bytes:
--      temp = temp || Hash(counter || num_bits_as_u32_be || input)
--      counter += 1
--    return temp[0..num_bytes]
def hash_df (input : (RustArray u8 400)) (input_len : usize) (num_bits : u32) :
    RustM (RustArray u8 55) := do
  let num_bytes : usize ←
    ((← ((← (Rust_primitives.Hax.cast_op num_bits)) +? (7 : usize)))
      /? (8 : usize));
  let result : (RustArray u8 55) ←
    (Rust_primitives.Hax.repeat (0 : u8) (55 : usize));
  let result_offset : usize := (0 : usize);
  let ⟨result, result_offset⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_HASH_DF_ITERS
      (fun ⟨result, result_offset⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk result result_offset)
      (fun ⟨result, result_offset⟩ counter_minus_1 =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge result_offset num_bytes)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk result result_offset))))
        else
          let counter : u8 ←
            (Core_models.Num.Impl_6.wrapping_add
              (← (Rust_primitives.Hax.cast_op counter_minus_1))
              (1 : u8));
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              hash_input
              (0 : usize)
              counter);
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              hash_input
              (1 : usize)
              (← (Rust_primitives.Hax.cast_op (← (num_bits >>>? (24 : i32))))));
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              hash_input
              (2 : usize)
              (← (Rust_primitives.Hax.cast_op (← (num_bits >>>? (16 : i32))))));
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              hash_input
              (3 : usize)
              (← (Rust_primitives.Hax.cast_op (← (num_bits >>>? (8 : i32))))));
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              hash_input
              (4 : usize)
              (← (Rust_primitives.Hax.cast_op num_bits)));
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (← (MAX_HASH_DF_INPUT_LEN -? (5 : usize)))
              (fun hash_input _ => (do (pure true) : RustM Bool))
              hash_input
              (fun hash_input i =>
                (do
                if (← (Rust_primitives.Hax.Machine_int.lt i input_len)) then
                  let hash_input : (RustArray u8 400) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      hash_input
                      (← ((5 : usize) +? i))
                      (← input[i]_?));
                  (pure hash_input)
                else
                  (pure hash_input) :
                RustM (RustArray u8 400))));
          let hash_input_len : usize ← ((5 : usize) +? input_len);
          let digest : (RustArray u8 32) ←
            (sha256 (← (Rust_primitives.unsize hash_input)) hash_input_len);
          let result : (RustArray u8 55) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              OUTLEN
              (fun result _ => (do (pure true) : RustM Bool))
              result
              (fun result i =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← (result_offset +? i))
                  num_bytes)) then
                  let result : (RustArray u8 55) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      result
                      (← (result_offset +? i))
                      (← digest[i]_?));
                  (pure result)
                else
                  (pure result) :
                RustM (RustArray u8 55))));
          let result_offset : usize ← (result_offset +? OUTLEN);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk result result_offset))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2 (RustArray u8 55) usize))
          (Rust_primitives.Hax.Tuple2 (RustArray u8 55) usize)))));
  (pure result)

--  Hash_DRBG Instantiate (SP 800-90A, Section 10.1.1.2).
-- 
--  seed_material = entropy || nonce || personalization_string
--  seed = Hash_df(seed_material, seedlen_bits)
--  V = seed
--  C = Hash_df(0x00 || V, seedlen_bits)
--  reseed_counter = 1
-- 
--  # Arguments
--  * `entropy` - Entropy input (at least seedlen bytes recommended)
--  * `entropy_len` - Length of entropy in bytes
--  * `nonce` - Nonce (at least half seedlen bytes recommended)
--  * `nonce_len` - Length of nonce in bytes
--  * `personalization` - Optional personalization string
--  * `perso_len` - Length of personalization string in bytes
def hash_drbg_instantiate
    (entropy : (RustArray u8 55))
    (entropy_len : usize)
    (nonce : (RustArray u8 32))
    (nonce_len : usize)
    (personalization : (RustArray u8 256))
    (perso_len : usize) :
    RustM HashDrbgState := do
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
  let offset : usize := (0 : usize);
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i entropy_len)) then
          let seed_material : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              (← (offset +? i))
              (← entropy[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 400))));
  let offset : usize ← (offset +? entropy_len);
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      OUTLEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i nonce_len)) then
          let seed_material : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              (← (offset +? i))
              (← nonce[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 400))));
  let offset : usize ← (offset +? nonce_len);
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_PERSONALIZATION_LEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i perso_len)) then
          let seed_material : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              (← (offset +? i))
              (← personalization[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 400))));
  let offset : usize ← (offset +? perso_len);
  let seed_material_len : usize := offset;
  let v : (RustArray u8 55) ←
    (hash_df
      seed_material
      seed_material_len
      (← ((← (Rust_primitives.Hax.cast_op SEEDLEN)) *? (8 : u32))));
  let c_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
  let c_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      c_input
      (0 : usize)
      (0 : u8));
  let c_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun c_input _ => (do (pure true) : RustM Bool))
      c_input
      (fun c_input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          c_input
          (← ((1 : usize) +? i))
          (← v[i]_?)) :
        RustM (RustArray u8 400))));
  let c : (RustArray u8 55) ←
    (hash_df
      c_input
      (← ((1 : usize) +? SEEDLEN))
      (← ((← (Rust_primitives.Hax.cast_op SEEDLEN)) *? (8 : u32))));
  (pure (HashDrbgState.mk (v := v) (c := c) (reseed_counter := (1 : u64))))

--  Hash_DRBG Reseed (SP 800-90A, Section 10.1.1.3).
-- 
--  seed_material = 0x01 || V || entropy || additional_input
--  seed = Hash_df(seed_material, seedlen_bits)
--  V = seed
--  C = Hash_df(0x00 || V, seedlen_bits)
--  reseed_counter = 1
def hash_drbg_reseed
    (state : HashDrbgState)
    (entropy : (RustArray u8 55))
    (entropy_len : usize)
    (additional_input : (RustArray u8 256))
    (additional_len : usize) :
    RustM HashDrbgState := do
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
  let offset : usize := (0 : usize);
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      seed_material
      (0 : usize)
      (1 : u8));
  let offset : usize ← (offset +? (1 : usize));
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          seed_material
          (← (offset +? i))
          (← (HashDrbgState.v state)[i]_?)) :
        RustM (RustArray u8 400))));
  let offset : usize ← (offset +? SEEDLEN);
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i entropy_len)) then
          let seed_material : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              (← (offset +? i))
              (← entropy[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 400))));
  let offset : usize ← (offset +? entropy_len);
  let seed_material : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_ADDITIONAL_INPUT_LEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i additional_len)) then
          let seed_material : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              (← (offset +? i))
              (← additional_input[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 400))));
  let offset : usize ← (offset +? additional_len);
  let seed_material_len : usize := offset;
  let v : (RustArray u8 55) ←
    (hash_df
      seed_material
      seed_material_len
      (← ((← (Rust_primitives.Hax.cast_op SEEDLEN)) *? (8 : u32))));
  let c_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
  let c_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      c_input
      (0 : usize)
      (0 : u8));
  let c_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun c_input _ => (do (pure true) : RustM Bool))
      c_input
      (fun c_input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          c_input
          (← ((1 : usize) +? i))
          (← v[i]_?)) :
        RustM (RustArray u8 400))));
  let c : (RustArray u8 55) ←
    (hash_df
      c_input
      (← ((1 : usize) +? SEEDLEN))
      (← ((← (Rust_primitives.Hax.cast_op SEEDLEN)) *? (8 : u32))));
  (pure (HashDrbgState.mk (v := v) (c := c) (reseed_counter := (1 : u64))))

--  Hashgen: generate pseudorandom bits using iterated hashing
--  (SP 800-90A, Section 10.1.1.4).
-- 
--  m = ceil(requested_bytes * 8 / outlen)  -- but outlen is in bits = 256
--  data = V (copy)
--  W = empty
--  for i in 1..m:
--    w = Hash(data)
--    W = W || w
--    data = (data + 1) mod 2^seedlen
--  return W[0..requested_bytes]
def hashgen
    (v : (RustArray u8 55))
    (requested_bytes : usize)
    (output : (RustArray u8 128)) :
    RustM (RustArray u8 128) := do
  let data : (RustArray u8 55) := v;
  let output_offset : usize := (0 : usize);
  let ⟨data, output, output_offset⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_HASHGEN_ITERS
      (fun ⟨data, output, output_offset⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple3.mk data output output_offset)
      (fun ⟨data, output, output_offset⟩ _i =>
        (do
        if
        (← (Rust_primitives.Hax.Machine_int.ge output_offset requested_bytes))
        then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple3.mk data output output_offset))))
        else
          let w : (RustArray u8 32) ←
            (sha256 (← (Rust_primitives.unsize data)) SEEDLEN);
          let output : (RustArray u8 128) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              OUTLEN
              (fun output _ => (do (pure true) : RustM Bool))
              output
              (fun output j =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← (output_offset +? j))
                  requested_bytes)) then
                  let output : (RustArray u8 128) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      output
                      (← (output_offset +? j))
                      (← w[j]_?));
                  (pure output)
                else
                  (pure output) :
                RustM (RustArray u8 128))));
          let output_offset : usize ← (output_offset +? OUTLEN);
          let data : (RustArray u8 55) ← (increment_mod_seedlen data);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple3.mk data output output_offset))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple3
              (RustArray u8 55)
              (RustArray u8 128)
              usize))
          (Rust_primitives.Hax.Tuple3
            (RustArray u8 55)
            (RustArray u8 128)
            usize)))));
  (pure output)

--  Hash_DRBG Generate (SP 800-90A, Section 10.1.1.4).
-- 
--  If additional_input is not empty:
--    w = Hash(0x02 || V || additional_input)
--    V = (V + w) mod 2^seedlen
-- 
--  returned_bits = Hashgen(requested_bytes, V)
-- 
--  H = Hash(0x03 || V)
--  V = (V + H + C + reseed_counter) mod 2^seedlen
--  reseed_counter += 1
-- 
--  Returns (output, new_state).
--  Helper: Build hash input for additional_input processing (Step 2).
--  Returns the updated V value.
def apply_additional_input
    (v : (RustArray u8 55))
    (additional_input : (RustArray u8 256))
    (additional_len : usize) :
    RustM (RustArray u8 55) := do
  let hash_input_len : usize ← ((← ((1 : usize) +? SEEDLEN)) +? additional_len);
  let hash_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
  let hash_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      hash_input
      (0 : usize)
      (2 : u8));
  let hash_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun hash_input _ => (do (pure true) : RustM Bool))
      hash_input
      (fun hash_input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          hash_input
          (← ((1 : usize) +? i))
          (← v[i]_?)) :
        RustM (RustArray u8 400))));
  let hash_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_ADDITIONAL_INPUT_LEN
      (fun hash_input _ => (do (pure true) : RustM Bool))
      hash_input
      (fun hash_input i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i additional_len)) then
          let hash_input : (RustArray u8 400) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              hash_input
              (← ((← ((1 : usize) +? SEEDLEN)) +? i))
              (← additional_input[i]_?));
          (pure hash_input)
        else
          (pure hash_input) :
        RustM (RustArray u8 400))));
  let w : (RustArray u8 32) ←
    (sha256 (← (Rust_primitives.unsize hash_input)) hash_input_len);
  let w_ext : (RustArray u8 55) ←
    (Rust_primitives.Hax.repeat (0 : u8) (55 : usize));
  let w_ext : (RustArray u8 55) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      OUTLEN
      (fun w_ext _ => (do (pure true) : RustM Bool))
      w_ext
      (fun w_ext i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          w_ext
          (← ((← (SEEDLEN -? OUTLEN)) +? i))
          (← w[i]_?)) :
        RustM (RustArray u8 55))));
  (add_mod_seedlen v w_ext)

--  Helper: Compute H = Hash(0x03 || V), extended to seedlen bytes.
def compute_h_ext (v : (RustArray u8 55)) : RustM (RustArray u8 55) := do
  let h_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.repeat (0 : u8) (400 : usize));
  let h_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      h_input
      (0 : usize)
      (3 : u8));
  let h_input : (RustArray u8 400) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun h_input _ => (do (pure true) : RustM Bool))
      h_input
      (fun h_input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          h_input
          (← ((1 : usize) +? i))
          (← v[i]_?)) :
        RustM (RustArray u8 400))));
  let h_digest : (RustArray u8 32) ←
    (sha256 (← (Rust_primitives.unsize h_input)) (← ((1 : usize) +? SEEDLEN)));
  let h_ext : (RustArray u8 55) ←
    (Rust_primitives.Hax.repeat (0 : u8) (55 : usize));
  let h_ext : (RustArray u8 55) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      OUTLEN
      (fun h_ext _ => (do (pure true) : RustM Bool))
      h_ext
      (fun h_ext i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          h_ext
          (← ((← (SEEDLEN -? OUTLEN)) +? i))
          (← h_digest[i]_?)) :
        RustM (RustArray u8 55))));
  (pure h_ext)

def hash_drbg_generate
    (state : HashDrbgState)
    (requested_bytes : usize)
    (additional_input : (RustArray u8 256))
    (additional_len : usize) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) HashDrbgState) := do
  let v : (RustArray u8 55) ←
    if (← (Rust_primitives.Hax.Machine_int.gt additional_len (0 : usize))) then
      (apply_additional_input
        (HashDrbgState.v state)
        additional_input
        additional_len)
    else
      (pure (HashDrbgState.v state));
  let output : (RustArray u8 128) ←
    (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
  let output : (RustArray u8 128) ← (hashgen v requested_bytes output);
  let h_ext : (RustArray u8 55) ← (compute_h_ext v);
  let v_plus_h : (RustArray u8 55) ← (add_mod_seedlen v h_ext);
  let v_plus_h_plus_c : (RustArray u8 55) ←
    (add_mod_seedlen v_plus_h (HashDrbgState.c state));
  let new_v : (RustArray u8 55) ←
    (add_u64_mod_seedlen v_plus_h_plus_c (HashDrbgState.reseed_counter state));
  let new_state : HashDrbgState :=
    (HashDrbgState.mk
      (v := new_v)
      (c := (HashDrbgState.c state))
      (reseed_counter := (← (Core_models.Num.Impl_9.wrapping_add
        (HashDrbgState.reseed_counter state)
        (1 : u64)))));
  (pure (Rust_primitives.Hax.Tuple2.mk output new_state))

end Hashdrbg_hax

