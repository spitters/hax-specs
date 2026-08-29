
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


namespace Hmacdrbg_hax

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

--  Maximum message length for SHA-256 bounded iteration: 512 bytes.
--  HMAC-DRBG builds messages up to V || 0x01 || seed_material, which
--  can be 32 + 1 + (entropy + nonce + perso). We set this generously.
def MAX_MSG_LEN : usize := (512 : usize)

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

--  Maximum output size per generate call (bytes).
--  Must be a multiple of SHA256_DIGEST_SIZE for simplicity.
def MAX_OUTPUT : usize := (128 : usize)

--  Maximum seed material length: entropy(32) + nonce(16) + personalization(up to 64).
def MAX_SEED_MATERIAL : usize := (128 : usize)

--  Maximum number of HMAC blocks generated in a single generate call.
--  MAX_OUTPUT / SHA256_DIGEST_SIZE = 128 / 32 = 4.
def MAX_GEN_BLOCKS : usize :=
  RustM.of_isOk (do (MAX_OUTPUT /? SHA256_DIGEST_SIZE)) (by rfl)

--  Maximum HMAC input for update: V(32) + 1 + seed_material(MAX_SEED_MATERIAL).
def MAX_HMAC_INPUT : usize :=
  RustM.of_isOk
    (do ((← (SHA256_DIGEST_SIZE +? (1 : usize))) +? MAX_SEED_MATERIAL))
    (by rfl)

--  HMAC-DRBG internal state (SP 800-90A, Section 10.1.2).
-- 
--  For HMAC-SHA-256:
--    - Key: 32 bytes
--    - V: 32 bytes
structure HmacDrbgState where
  key : (RustArray u8 32)
  v : (RustArray u8 32)

@[instance] opaque Impl_3.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes HmacDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  Core_models.Clone.Clone HmacDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes HmacDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  Core_models.Marker.Copy HmacDrbgState :=
  by constructor <;> exact Inhabited.default

--  HMAC-DRBG Update function (SP 800-90A, Section 10.1.2.2).
-- 
--  Update(K, V, provided_data):
--    K = HMAC(K, V || 0x00 || provided_data)
--    V = HMAC(K, V)
--    if provided_data is not empty:
--      K = HMAC(K, V || 0x01 || provided_data)
--      V = HMAC(K, V)
def hmac_drbg_update
    (state : HmacDrbgState)
    (provided_data : (RustSlice u8))
    (provided_data_len : usize) :
    RustM HmacDrbgState := do
  let msg : (RustArray u8 161) ←
    (Rust_primitives.Hax.repeat (0 : u8) (161 : usize));
  let msg : (RustArray u8 161) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SHA256_DIGEST_SIZE
      (fun msg _ => (do (pure true) : RustM Bool))
      msg
      (fun msg i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          msg
          i
          (← (HmacDrbgState.v state)[i]_?)) :
        RustM (RustArray u8 161))));
  let msg : (RustArray u8 161) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      msg
      SHA256_DIGEST_SIZE
      (0 : u8));
  let msg : (RustArray u8 161) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_SEED_MATERIAL
      (fun msg _ => (do (pure true) : RustM Bool))
      msg
      (fun msg i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i provided_data_len)) then
          let msg : (RustArray u8 161) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              msg
              (← ((← (SHA256_DIGEST_SIZE +? (1 : usize))) +? i))
              (← provided_data[i]_?));
          (pure msg)
        else
          (pure msg) :
        RustM (RustArray u8 161))));
  let msg_len : usize ←
    ((← (SHA256_DIGEST_SIZE +? (1 : usize))) +? provided_data_len);
  let new_key : (RustArray u8 32) ←
    (hmac_sha256
      (← (Rust_primitives.unsize (HmacDrbgState.key state)))
      SHA256_DIGEST_SIZE
      (← (Rust_primitives.unsize msg))
      msg_len);
  let new_v : (RustArray u8 32) ←
    (hmac_sha256
      (← (Rust_primitives.unsize new_key))
      SHA256_DIGEST_SIZE
      (← (Rust_primitives.unsize (HmacDrbgState.v state)))
      SHA256_DIGEST_SIZE);
  if (← (Rust_primitives.Hax.Machine_int.eq provided_data_len (0 : usize))) then
    (pure (HmacDrbgState.mk (key := new_key) (v := new_v)))
  else
    let msg2 : (RustArray u8 161) ←
      (Rust_primitives.Hax.repeat (0 : u8) (161 : usize));
    let msg2 : (RustArray u8 161) ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        SHA256_DIGEST_SIZE
        (fun msg2 _ => (do (pure true) : RustM Bool))
        msg2
        (fun msg2 i =>
          (do
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            msg2
            i
            (← new_v[i]_?)) :
          RustM (RustArray u8 161))));
    let msg2 : (RustArray u8 161) ←
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        msg2
        SHA256_DIGEST_SIZE
        (1 : u8));
    let msg2 : (RustArray u8 161) ←
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        MAX_SEED_MATERIAL
        (fun msg2 _ => (do (pure true) : RustM Bool))
        msg2
        (fun msg2 i =>
          (do
          if (← (Rust_primitives.Hax.Machine_int.lt i provided_data_len)) then
            let msg2 : (RustArray u8 161) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                msg2
                (← ((← (SHA256_DIGEST_SIZE +? (1 : usize))) +? i))
                (← provided_data[i]_?));
            (pure msg2)
          else
            (pure msg2) :
          RustM (RustArray u8 161))));
    let msg2_len : usize ←
      ((← (SHA256_DIGEST_SIZE +? (1 : usize))) +? provided_data_len);
    let new_key2 : (RustArray u8 32) ←
      (hmac_sha256
        (← (Rust_primitives.unsize new_key))
        SHA256_DIGEST_SIZE
        (← (Rust_primitives.unsize msg2))
        msg2_len);
    let new_v2 : (RustArray u8 32) ←
      (hmac_sha256
        (← (Rust_primitives.unsize new_key2))
        SHA256_DIGEST_SIZE
        (← (Rust_primitives.unsize new_v))
        SHA256_DIGEST_SIZE);
    (pure (HmacDrbgState.mk (key := new_key2) (v := new_v2)))

--  HMAC-DRBG Instantiate function (SP 800-90A, Section 10.1.2.3).
-- 
--  Instantiate(entropy, nonce, personalization):
--    K = 0x00 * 32
--    V = 0x01 * 32
--    seed_material = entropy || nonce || personalization
--    (K, V) = Update(seed_material, K, V)
def hmac_drbg_instantiate
    (entropy : (RustSlice u8))
    (entropy_len : usize)
    (nonce : (RustSlice u8))
    (nonce_len : usize)
    (personalization : (RustSlice u8))
    (personalization_len : usize) :
    RustM HmacDrbgState := do
  let key : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let v : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (1 : u8) (32 : usize));
  let key : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SHA256_DIGEST_SIZE
      (fun key _ => (do (pure true) : RustM Bool))
      key
      (fun key i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          key
          i
          (0 : u8)) :
        RustM (RustArray u8 32))));
  let v : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SHA256_DIGEST_SIZE
      (fun v _ => (do (pure true) : RustM Bool))
      v
      (fun v i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          v
          i
          (1 : u8)) :
        RustM (RustArray u8 32))));
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
  let offset : usize := (0 : usize);
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_SEED_MATERIAL
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i entropy_len)) then
          let seed_material : (RustArray u8 128) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              (← (offset +? i))
              (← entropy[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 128))));
  let offset : usize ← (offset +? entropy_len);
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_SEED_MATERIAL
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i nonce_len)) then
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← (offset +? i))
            MAX_SEED_MATERIAL)) then
            let seed_material : (RustArray u8 128) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                seed_material
                (← (offset +? i))
                (← nonce[i]_?));
            (pure seed_material)
          else
            (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 128))));
  let offset : usize ← (offset +? nonce_len);
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_SEED_MATERIAL
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i personalization_len)) then
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← (offset +? i))
            MAX_SEED_MATERIAL)) then
            let seed_material : (RustArray u8 128) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                seed_material
                (← (offset +? i))
                (← personalization[i]_?));
            (pure seed_material)
          else
            (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 128))));
  let offset : usize ← (offset +? personalization_len);
  let seed_len : usize := offset;
  let initial_state : HmacDrbgState := (HmacDrbgState.mk (key := key) (v := v));
  (hmac_drbg_update
    initial_state
    (← (Rust_primitives.unsize seed_material))
    seed_len)

--  HMAC-DRBG Generate function (SP 800-90A, Section 10.1.2.5).
-- 
--  Generate(state, requested_bytes, additional_input):
--    if additional_input is not empty:
--      (K, V) = Update(additional_input)
--    temp = empty
--    while len(temp) < requested_bytes:
--      V = HMAC(K, V)
--      temp = temp || V
--    (K, V) = Update(additional_input)
--    return temp[0..requested_bytes]
-- 
--  `num_bytes` must be <= MAX_OUTPUT.
def hmac_drbg_generate
    (state : HmacDrbgState)
    (num_bytes : usize)
    (additional_input : (RustSlice u8))
    (additional_input_len : usize) :
    RustM (Rust_primitives.Hax.Tuple2 HmacDrbgState (RustArray u8 128)) := do
  let working_state : HmacDrbgState ←
    if
    (← (Rust_primitives.Hax.Machine_int.gt additional_input_len (0 : usize)))
    then
      (hmac_drbg_update state additional_input additional_input_len)
    else
      (pure state);
  let output : (RustArray u8 128) ←
    (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
  let current_v : (RustArray u8 32) := (HmacDrbgState.v working_state);
  let generated : usize := (0 : usize);
  let ⟨current_v, generated, output⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_GEN_BLOCKS
      (fun ⟨current_v, generated, output⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple3.mk current_v generated output)
      (fun ⟨current_v, generated, output⟩ _block =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge generated num_bytes)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple3.mk current_v generated output))))
        else
          let current_v : (RustArray u8 32) ←
            (hmac_sha256
              (← (Rust_primitives.unsize (HmacDrbgState.key working_state)))
              SHA256_DIGEST_SIZE
              (← (Rust_primitives.unsize current_v))
              SHA256_DIGEST_SIZE);
          let output : (RustArray u8 128) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              SHA256_DIGEST_SIZE
              (fun output _ => (do (pure true) : RustM Bool))
              output
              (fun output i =>
                (do
                if
                (← ((← (Rust_primitives.Hax.Machine_int.lt
                    (← (generated +? i))
                    num_bytes))
                  &&? (← (Rust_primitives.Hax.Machine_int.lt
                    (← (generated +? i))
                    MAX_OUTPUT)))) then
                  let output : (RustArray u8 128) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      output
                      (← (generated +? i))
                      (← current_v[i]_?));
                  (pure output)
                else
                  (pure output) :
                RustM (RustArray u8 128))));
          let generated : usize ← (generated +? SHA256_DIGEST_SIZE);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple3.mk current_v generated output))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple3
              (RustArray u8 32)
              usize
              (RustArray u8 128)))
          (Rust_primitives.Hax.Tuple3
            (RustArray u8 32)
            usize
            (RustArray u8 128))))));
  let updated_state : HmacDrbgState :=
    (HmacDrbgState.mk
      (key := (HmacDrbgState.key working_state))
      (v := current_v));
  let final_state : HmacDrbgState ←
    (hmac_drbg_update updated_state additional_input additional_input_len);
  (pure (Rust_primitives.Hax.Tuple2.mk final_state output))

--  HMAC-DRBG Reseed function (SP 800-90A, Section 10.1.2.4).
-- 
--  Reseed(state, entropy, additional_input):
--    seed_material = entropy || additional_input
--    (K, V) = Update(seed_material, K, V)
def hmac_drbg_reseed
    (state : HmacDrbgState)
    (entropy : (RustSlice u8))
    (entropy_len : usize)
    (additional : (RustSlice u8))
    (additional_len : usize) :
    RustM HmacDrbgState := do
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_SEED_MATERIAL
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i entropy_len)) then
          let seed_material : (RustArray u8 128) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              seed_material
              i
              (← entropy[i]_?));
          (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 128))));
  let seed_material : (RustArray u8 128) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      MAX_SEED_MATERIAL
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i additional_len)) then
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← (entropy_len +? i))
            MAX_SEED_MATERIAL)) then
            let seed_material : (RustArray u8 128) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                seed_material
                (← (entropy_len +? i))
                (← additional[i]_?));
            (pure seed_material)
          else
            (pure seed_material)
        else
          (pure seed_material) :
        RustM (RustArray u8 128))));
  let seed_len : usize ← (entropy_len +? additional_len);
  (hmac_drbg_update state (← (Rust_primitives.unsize seed_material)) seed_len)

end Hmacdrbg_hax

