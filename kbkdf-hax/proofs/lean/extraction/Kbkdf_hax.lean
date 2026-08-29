
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


namespace Kbkdf_hax

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

--  SHA-256 digest size in bytes.
def SHA256_DIGEST_SIZE : usize := (32 : usize)

--  Maximum message length for SHA-256/HMAC: 256 bytes (for hax bounded iteration).
def MAX_MSG_LEN : usize := (256 : usize)

--  SHA-256 state.
structure Sha256State where
  h : (RustArray u32 8)
  buf : (RustArray u8 64)
  buf_len : usize
  total_len : u64

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes Sha256State :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Clone.Clone Sha256State :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes Sha256State :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Marker.Copy Sha256State :=
  by constructor <;> exact Inhabited.default

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
      (← ((← ((← (MAX_MSG_LEN +? (← (SHA256_BLOCK_SIZE *? (2 : usize)))))
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

--  HMAC key: up to 64 bytes (SHA-256 block size). Keys longer than 64 bytes
--  are first hashed to 32 bytes.
abbrev HmacKey : Type := (RustArray u8 64)

--  HMAC tag: 32 bytes (SHA-256 output).
abbrev HmacTag : Type := (RustArray u8 32)

--  Prepare HMAC key: if key > block_size, hash it; then zero-pad to block_size.
def hmac_prepare_key (key : (RustSlice u8)) (key_len : usize) :
    RustM (RustArray u8 64) := do
  let k_prime : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let k_prime : (RustArray u8 64) ←
    if (← (Rust_primitives.Hax.Machine_int.gt key_len SHA256_BLOCK_SIZE)) then
      let hashed : (RustArray u8 32) ← (sha256 key key_len);
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        SHA256_DIGEST_SIZE
        (fun k_prime _ => (do (pure true) : RustM Bool))
        k_prime
        (fun k_prime i =>
          (do
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            k_prime
            i
            (← hashed[i]_?)) :
          RustM (RustArray u8 64))))
    else
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        SHA256_BLOCK_SIZE
        (fun k_prime _ => (do (pure true) : RustM Bool))
        k_prime
        (fun k_prime i =>
          (do
          if (← (Rust_primitives.Hax.Machine_int.lt i key_len)) then
            let k_prime : (RustArray u8 64) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                k_prime
                i
                (← key[i]_?));
            (pure k_prime)
          else
            (pure k_prime) :
          RustM (RustArray u8 64))));
  (pure k_prime)

--  HMAC-SHA-256 computation.
-- 
--  HMAC(K, M) = H((K' XOR opad) || H((K' XOR ipad) || M))
-- 
--  where ipad = 0x36 * 64, opad = 0x5c * 64.
def hmac_sha256
    (key : (RustSlice u8))
    (key_len : usize)
    (msg : (RustSlice u8))
    (msg_len : usize) :
    RustM (RustArray u8 32) := do
  let k_prime : (RustArray u8 64) ← (hmac_prepare_key key key_len);
  let ipad_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let ipad_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SHA256_BLOCK_SIZE
      (fun ipad_key _ => (do (pure true) : RustM Bool))
      ipad_key
      (fun ipad_key i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          ipad_key
          i
          (← ((← k_prime[i]_?) ^^^? (54 : u8)))) :
        RustM (RustArray u8 64))));
  let inner_state : Sha256State ← (Impl.new Rust_primitives.Hax.Tuple0.mk);
  let inner_state : Sha256State ←
    (sha256_update
      inner_state
      (← (Rust_primitives.unsize ipad_key))
      SHA256_BLOCK_SIZE);
  let inner_state : Sha256State ← (sha256_update inner_state msg msg_len);
  let inner_hash : (RustArray u8 32) ← (sha256_finalize inner_state);
  let opad_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let opad_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SHA256_BLOCK_SIZE
      (fun opad_key _ => (do (pure true) : RustM Bool))
      opad_key
      (fun opad_key i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          opad_key
          i
          (← ((← k_prime[i]_?) ^^^? (92 : u8)))) :
        RustM (RustArray u8 64))));
  let outer_state : Sha256State ← (Impl.new Rust_primitives.Hax.Tuple0.mk);
  let outer_state : Sha256State ←
    (sha256_update
      outer_state
      (← (Rust_primitives.unsize opad_key))
      SHA256_BLOCK_SIZE);
  let outer_state : Sha256State ←
    (sha256_update
      outer_state
      (← (Rust_primitives.unsize inner_hash))
      SHA256_DIGEST_SIZE);
  (sha256_finalize outer_state)

--  Maximum derived key length in bytes (2 HMAC-SHA-256 blocks = 64 bytes = 512 bits).
def MAX_DK_LEN : usize := (64 : usize)

--  Maximum number of HMAC blocks (ceil(MAX_DK_LEN / SHA256_DIGEST_SIZE)).
def MAX_BLOCKS : usize := (2 : usize)

--  Maximum label length in bytes.
def MAX_LABEL_LEN : usize := (32 : usize)

--  Maximum context length in bytes.
def MAX_CONTEXT_LEN : usize := (64 : usize)

--  Counter length in bytes (r = 32 bits).
def COUNTER_LEN : usize := (4 : usize)

--  Maximum fixed input data length in bytes:
--    MAX_LABEL_LEN + 1 (separator) + MAX_CONTEXT_LEN + 4 (L encoding)
--    = 32 + 1 + 64 + 4 = 101
def MAX_FIXED_LEN : usize :=
  RustM.of_isOk
    (do
    ((← ((← (MAX_LABEL_LEN +? (1 : usize))) +? MAX_CONTEXT_LEN))
      +? (4 : usize)))
    (by rfl)

--  Maximum PRF input buffer size: COUNTER_LEN + MAX_FIXED_LEN = 105.
def MAX_PRF_INPUT_LEN : usize :=
  RustM.of_isOk (do (COUNTER_LEN +? MAX_FIXED_LEN)) (by rfl)

--  Key derivation key: 32 bytes (for HMAC-SHA-256).
abbrev KbkdfKey : Type := (RustArray u8 32)

--  Derived key output buffer: MAX_DK_LEN bytes.
abbrev DerivedKey : Type := (RustArray u8 64)

--  KBKDF in Counter Mode with HMAC-SHA-256 as PRF over opaque fixed input
--  data (SP 800-108 Rev. 1, Section 4.1), counter before the fixed input
--  data, r = 32.
-- 
--  # Arguments
--  * `ki` - Key derivation key (32 bytes)
--  * `fixed` - Fixed input data (up to MAX_FIXED_LEN bytes)
--  * `fixed_len` - Actual length of the fixed input data
--  * `output_bits` - Desired output length L in bits (a multiple of 8,
--    at most MAX_DK_LEN * 8 = 512)
-- 
--  # Returns
--  Fixed-size array of MAX_DK_LEN bytes; only the first `output_bits / 8` bytes
--  are meaningful, the rest are zero.
-- 
--  # Algorithm
--  ```text
--  n = ceil(output_bits / 256)
--  For i = 1..n:
--    K(i) = HMAC-SHA-256(KI, [i]_4 || FixedInputData)
--  K_OUT = K(1) || K(2) || ... || K(n), truncated to output_bits/8 bytes
--  ```
def kbkdf_counter_hmac256_fixed
    (ki : (RustArray u8 32))
    (fixed : (RustSlice u8))
    (fixed_len : usize)
    (output_bits : u32) :
    RustM (RustArray u8 64) := do
  let output_bytes : usize ←
    (Rust_primitives.Hax.cast_op (← (output_bits /? (8 : u32))));
  let n : usize ←
    if (← (Rust_primitives.Hax.Machine_int.eq output_bits (0 : u32))) then
      (pure (0 : usize))
    else
      ((← ((← (Rust_primitives.Hax.cast_op output_bits)) +? (255 : usize)))
        /? (256 : usize));
  let dk : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let prf_input : (RustArray u8 105) ←
    (Rust_primitives.Hax.repeat (0 : u8) (105 : usize));
  let prf_input : (RustArray u8 105) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_FIXED_LEN
      (fun prf_input _ => (do (pure true) : RustM Bool))
      prf_input
      (fun prf_input i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i fixed_len)) then
          let prf_input : (RustArray u8 105) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              prf_input
              (← (COUNTER_LEN +? i))
              (← fixed[i]_?));
          (pure prf_input)
        else
          (pure prf_input) :
        RustM (RustArray u8 105))));
  let prf_len : usize ← (COUNTER_LEN +? fixed_len);
  let ⟨dk, prf_input⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun ⟨dk, prf_input⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk dk prf_input)
      (fun ⟨dk, prf_input⟩ block_idx =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge block_idx n)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk dk prf_input))))
        else
          let counter : u32 ←
            (Core_models.Num.Impl_8.wrapping_add
              (← (Rust_primitives.Hax.cast_op block_idx))
              (1 : u32));
          let prf_input : (RustArray u8 105) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              prf_input
              (0 : usize)
              (← (Rust_primitives.Hax.cast_op (← (counter >>>? (24 : i32))))));
          let prf_input : (RustArray u8 105) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              prf_input
              (1 : usize)
              (← (Rust_primitives.Hax.cast_op (← (counter >>>? (16 : i32))))));
          let prf_input : (RustArray u8 105) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              prf_input
              (2 : usize)
              (← (Rust_primitives.Hax.cast_op (← (counter >>>? (8 : i32))))));
          let prf_input : (RustArray u8 105) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              prf_input
              (3 : usize)
              (← (Rust_primitives.Hax.cast_op counter)));
          let block_mac : (RustArray u8 32) ←
            (hmac_sha256
              (← (Rust_primitives.unsize ki))
              SHA256_DIGEST_SIZE
              (← (Rust_primitives.unsize prf_input))
              prf_len);
          let offset : usize ← (block_idx *? SHA256_DIGEST_SIZE);
          let dk : (RustArray u8 64) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              SHA256_DIGEST_SIZE
              (fun dk _ => (do (pure true) : RustM Bool))
              dk
              (fun dk j =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← (offset +? j))
                  output_bytes)) then
                  let dk : (RustArray u8 64) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      dk
                      (← (offset +? j))
                      (← block_mac[j]_?));
                  (pure dk)
                else
                  (pure dk) :
                RustM (RustArray u8 64))));
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk dk prf_input))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2 (RustArray u8 64) (RustArray u8 105)))
          (Rust_primitives.Hax.Tuple2 (RustArray u8 64) (RustArray u8 105))))));
  (pure dk)

--  KBKDF in Counter Mode with HMAC-SHA-256 as PRF and the fixed input data
--  `Label || 0x00 || Context || [L]_4` (SP 800-108 Rev. 1, Section 4).
-- 
--  # Arguments
--  * `ki` - Key derivation key (32 bytes)
--  * `label` - Label byte string (up to MAX_LABEL_LEN bytes)
--  * `label_len` - Actual length of label
--  * `context` - Context byte string (up to MAX_CONTEXT_LEN bytes)
--  * `context_len` - Actual length of context
--  * `output_bits` - Desired output length L in bits (a multiple of 8,
--    at most MAX_DK_LEN * 8 = 512)
-- 
--  # Returns
--  Fixed-size array of MAX_DK_LEN bytes; only the first `output_bits / 8` bytes
--  are meaningful, the rest are zero.
-- 
--  # Algorithm
--  ```text
--  n = ceil(output_bits / 256)
--  For i = 1..n:
--    K(i) = HMAC-SHA-256(KI, [i]_4 || Label || 0x00 || Context || [L]_4)
--  K_OUT = K(1) || K(2) || ... || K(n), truncated to output_bits/8 bytes
--  ```
def kbkdf_counter_hmac256
    (ki : (RustArray u8 32))
    (label : (RustSlice u8))
    (label_len : usize)
    (context : (RustSlice u8))
    (context_len : usize)
    (output_bits : u32) :
    RustM (RustArray u8 64) := do
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.repeat (0 : u8) (101 : usize));
  let fixed_len : usize := (0 : usize);
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_LABEL_LEN
      (fun fixed _ => (do (pure true) : RustM Bool))
      fixed
      (fun fixed i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i label_len)) then
          let fixed : (RustArray u8 101) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              fixed
              (← (fixed_len +? i))
              (← label[i]_?));
          (pure fixed)
        else
          (pure fixed) :
        RustM (RustArray u8 101))));
  let fixed_len : usize ← (fixed_len +? label_len);
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      fixed
      fixed_len
      (0 : u8));
  let fixed_len : usize ← (fixed_len +? (1 : usize));
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_CONTEXT_LEN
      (fun fixed _ => (do (pure true) : RustM Bool))
      fixed
      (fun fixed i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i context_len)) then
          let fixed : (RustArray u8 101) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              fixed
              (← (fixed_len +? i))
              (← context[i]_?));
          (pure fixed)
        else
          (pure fixed) :
        RustM (RustArray u8 101))));
  let fixed_len : usize ← (fixed_len +? context_len);
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      fixed
      fixed_len
      (← (Rust_primitives.Hax.cast_op (← (output_bits >>>? (24 : i32))))));
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      fixed
      (← (fixed_len +? (1 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (output_bits >>>? (16 : i32))))));
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      fixed
      (← (fixed_len +? (2 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (output_bits >>>? (8 : i32))))));
  let fixed : (RustArray u8 101) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      fixed
      (← (fixed_len +? (3 : usize)))
      (← (Rust_primitives.Hax.cast_op output_bits)));
  let fixed_len : usize ← (fixed_len +? (4 : usize));
  (kbkdf_counter_hmac256_fixed
    ki
    (← (Rust_primitives.unsize fixed))
    fixed_len
    output_bits)

end Kbkdf_hax

