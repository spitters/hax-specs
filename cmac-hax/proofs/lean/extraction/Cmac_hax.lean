
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


namespace Cmac_hax

--  AES S-box lookup table (FIPS 197, Figure 7).
def AES_SBOX : (RustArray u8 256) :=
  RustM.of_isOk
    (do
    #v[(99 : u8),
         (124 : u8),
         (119 : u8),
         (123 : u8),
         (242 : u8),
         (107 : u8),
         (111 : u8),
         (197 : u8),
         (48 : u8),
         (1 : u8),
         (103 : u8),
         (43 : u8),
         (254 : u8),
         (215 : u8),
         (171 : u8),
         (118 : u8),
         (202 : u8),
         (130 : u8),
         (201 : u8),
         (125 : u8),
         (250 : u8),
         (89 : u8),
         (71 : u8),
         (240 : u8),
         (173 : u8),
         (212 : u8),
         (162 : u8),
         (175 : u8),
         (156 : u8),
         (164 : u8),
         (114 : u8),
         (192 : u8),
         (183 : u8),
         (253 : u8),
         (147 : u8),
         (38 : u8),
         (54 : u8),
         (63 : u8),
         (247 : u8),
         (204 : u8),
         (52 : u8),
         (165 : u8),
         (229 : u8),
         (241 : u8),
         (113 : u8),
         (216 : u8),
         (49 : u8),
         (21 : u8),
         (4 : u8),
         (199 : u8),
         (35 : u8),
         (195 : u8),
         (24 : u8),
         (150 : u8),
         (5 : u8),
         (154 : u8),
         (7 : u8),
         (18 : u8),
         (128 : u8),
         (226 : u8),
         (235 : u8),
         (39 : u8),
         (178 : u8),
         (117 : u8),
         (9 : u8),
         (131 : u8),
         (44 : u8),
         (26 : u8),
         (27 : u8),
         (110 : u8),
         (90 : u8),
         (160 : u8),
         (82 : u8),
         (59 : u8),
         (214 : u8),
         (179 : u8),
         (41 : u8),
         (227 : u8),
         (47 : u8),
         (132 : u8),
         (83 : u8),
         (209 : u8),
         (0 : u8),
         (237 : u8),
         (32 : u8),
         (252 : u8),
         (177 : u8),
         (91 : u8),
         (106 : u8),
         (203 : u8),
         (190 : u8),
         (57 : u8),
         (74 : u8),
         (76 : u8),
         (88 : u8),
         (207 : u8),
         (208 : u8),
         (239 : u8),
         (170 : u8),
         (251 : u8),
         (67 : u8),
         (77 : u8),
         (51 : u8),
         (133 : u8),
         (69 : u8),
         (249 : u8),
         (2 : u8),
         (127 : u8),
         (80 : u8),
         (60 : u8),
         (159 : u8),
         (168 : u8),
         (81 : u8),
         (163 : u8),
         (64 : u8),
         (143 : u8),
         (146 : u8),
         (157 : u8),
         (56 : u8),
         (245 : u8),
         (188 : u8),
         (182 : u8),
         (218 : u8),
         (33 : u8),
         (16 : u8),
         (255 : u8),
         (243 : u8),
         (210 : u8),
         (205 : u8),
         (12 : u8),
         (19 : u8),
         (236 : u8),
         (95 : u8),
         (151 : u8),
         (68 : u8),
         (23 : u8),
         (196 : u8),
         (167 : u8),
         (126 : u8),
         (61 : u8),
         (100 : u8),
         (93 : u8),
         (25 : u8),
         (115 : u8),
         (96 : u8),
         (129 : u8),
         (79 : u8),
         (220 : u8),
         (34 : u8),
         (42 : u8),
         (144 : u8),
         (136 : u8),
         (70 : u8),
         (238 : u8),
         (184 : u8),
         (20 : u8),
         (222 : u8),
         (94 : u8),
         (11 : u8),
         (219 : u8),
         (224 : u8),
         (50 : u8),
         (58 : u8),
         (10 : u8),
         (73 : u8),
         (6 : u8),
         (36 : u8),
         (92 : u8),
         (194 : u8),
         (211 : u8),
         (172 : u8),
         (98 : u8),
         (145 : u8),
         (149 : u8),
         (228 : u8),
         (121 : u8),
         (231 : u8),
         (200 : u8),
         (55 : u8),
         (109 : u8),
         (141 : u8),
         (213 : u8),
         (78 : u8),
         (169 : u8),
         (108 : u8),
         (86 : u8),
         (244 : u8),
         (234 : u8),
         (101 : u8),
         (122 : u8),
         (174 : u8),
         (8 : u8),
         (186 : u8),
         (120 : u8),
         (37 : u8),
         (46 : u8),
         (28 : u8),
         (166 : u8),
         (180 : u8),
         (198 : u8),
         (232 : u8),
         (221 : u8),
         (116 : u8),
         (31 : u8),
         (75 : u8),
         (189 : u8),
         (139 : u8),
         (138 : u8),
         (112 : u8),
         (62 : u8),
         (181 : u8),
         (102 : u8),
         (72 : u8),
         (3 : u8),
         (246 : u8),
         (14 : u8),
         (97 : u8),
         (53 : u8),
         (87 : u8),
         (185 : u8),
         (134 : u8),
         (193 : u8),
         (29 : u8),
         (158 : u8),
         (225 : u8),
         (248 : u8),
         (152 : u8),
         (17 : u8),
         (105 : u8),
         (217 : u8),
         (142 : u8),
         (148 : u8),
         (155 : u8),
         (30 : u8),
         (135 : u8),
         (233 : u8),
         (206 : u8),
         (85 : u8),
         (40 : u8),
         (223 : u8),
         (140 : u8),
         (161 : u8),
         (137 : u8),
         (13 : u8),
         (191 : u8),
         (230 : u8),
         (66 : u8),
         (104 : u8),
         (65 : u8),
         (153 : u8),
         (45 : u8),
         (15 : u8),
         (176 : u8),
         (84 : u8),
         (187 : u8),
         (22 : u8)])
    (by rfl)

--  AES round constants (FIPS 197, Section 5.2).
def RCON : (RustArray u8 10) :=
  RustM.of_isOk
    (do
    #v[(1 : u8),
         (2 : u8),
         (4 : u8),
         (8 : u8),
         (16 : u8),
         (32 : u8),
         (64 : u8),
         (128 : u8),
         (27 : u8),
         (54 : u8)])
    (by rfl)

--  A 128-bit block (16 bytes).
abbrev Block : Type := (RustArray u8 16)

--  AES-128 key: 16 bytes.
abbrev AesKey : Type := (RustArray u8 16)

--  AES-128 round keys: 11 x 16 bytes (initial + 10 rounds).
abbrev RoundKeys : Type := (RustArray (RustArray u8 16) 11)

--  Zero block constant.
def ZERO_BLOCK : (RustArray u8 16) :=
  RustM.of_isOk (do (Rust_primitives.Hax.repeat (0 : u8) (16 : usize))) (by rfl)

--  Maximum message length for bounded iteration: 64 blocks = 1024 bytes.
def MAX_BLOCKS : usize := (64 : usize)

--  XOR two 128-bit blocks.
def xor_block (a : (RustArray u8 16)) (b : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          i
          (← ((← a[i]_?) ^^^? (← b[i]_?)))) :
        RustM (RustArray u8 16))));
  (pure result)

--  Multiply by 2 in GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1.
def gf_mul2 (x : u8) : RustM u8 := do
  let shifted : u16 ← ((← (Rust_primitives.Hax.cast_op x)) <<<? (1 : i32));
  let reduced : u16 ←
    if
    (← (Rust_primitives.Hax.Machine_int.ne (← (x &&&? (128 : u8))) (0 : u8)))
    then
      (shifted ^^^? (27 : u16))
    else
      (pure shifted);
  (Rust_primitives.Hax.cast_op reduced)

--  Multiply by 3 in GF(2^8): 3*x = 2*x XOR x.
def gf_mul3 (x : u8) : RustM u8 := do ((← (gf_mul2 x)) ^^^? x)

--  AES SubBytes on a single word (4 bytes).
def sub_word (w : (RustArray u8 4)) : RustM (RustArray u8 4) := do
  (pure #v[(← AES_SBOX[
               (← (Rust_primitives.Hax.cast_op (← w[(0 : usize)]_?)))
               ]_?),
             (← AES_SBOX[
               (← (Rust_primitives.Hax.cast_op (← w[(1 : usize)]_?)))
               ]_?),
             (← AES_SBOX[
               (← (Rust_primitives.Hax.cast_op (← w[(2 : usize)]_?)))
               ]_?),
             (← AES_SBOX[
               (← (Rust_primitives.Hax.cast_op (← w[(3 : usize)]_?)))
               ]_?)])

--  AES RotWord: rotate 4 bytes left by 1.
def rot_word (w : (RustArray u8 4)) : RustM (RustArray u8 4) := do
  (pure #v[(← w[(1 : usize)]_?),
             (← w[(2 : usize)]_?),
             (← w[(3 : usize)]_?),
             (← w[(0 : usize)]_?)])

--  AES-128 key expansion: produce 11 round keys from 16-byte key.
-- 
--  Maps to CatCrypt's AES key schedule.
def aes128_key_expansion (key : (RustArray u8 16)) :
    RustM (RustArray (RustArray u8 16) 11) := do
  let rk : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (11 : usize));
  let rk : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun rk _ => (do (pure true) : RustM Bool))
      rk
      (fun rk i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          rk
          (0 : usize)
          (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            (← rk[(0 : usize)]_?)
            i
            (← key[i]_?)))) :
        RustM (RustArray (RustArray u8 16) 11))));
  let rk : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      (11 : usize)
      (fun rk _ => (do (pure true) : RustM Bool))
      rk
      (fun rk round =>
        (do
        let prev_last : (RustArray u8 4) :=
          #v[(← (← rk[(← (round -? (1 : usize)))]_?)[(12 : usize)]_?),
               (← (← rk[(← (round -? (1 : usize)))]_?)[(13 : usize)]_?),
               (← (← rk[(← (round -? (1 : usize)))]_?)[(14 : usize)]_?),
               (← (← rk[(← (round -? (1 : usize)))]_?)[(15 : usize)]_?)];
        let rotated : (RustArray u8 4) ← (rot_word prev_last);
        let subbed : (RustArray u8 4) ← (sub_word rotated);
        let rcon_byte : u8 ← RCON[(← (round -? (1 : usize)))]_?;
        let rk : (RustArray (RustArray u8 16) 11) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            rk
            round
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← rk[round]_?)
              (0 : usize)
              (← ((← ((← (← rk[(← (round -? (1 : usize)))]_?)[(0 : usize)]_?)
                  ^^^? (← subbed[(0 : usize)]_?)))
                ^^^? rcon_byte)))));
        let rk : (RustArray (RustArray u8 16) 11) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            rk
            round
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← rk[round]_?)
              (1 : usize)
              (← ((← (← rk[(← (round -? (1 : usize)))]_?)[(1 : usize)]_?)
                ^^^? (← subbed[(1 : usize)]_?))))));
        let rk : (RustArray (RustArray u8 16) 11) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            rk
            round
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← rk[round]_?)
              (2 : usize)
              (← ((← (← rk[(← (round -? (1 : usize)))]_?)[(2 : usize)]_?)
                ^^^? (← subbed[(2 : usize)]_?))))));
        let rk : (RustArray (RustArray u8 16) 11) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            rk
            round
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← rk[round]_?)
              (3 : usize)
              (← ((← (← rk[(← (round -? (1 : usize)))]_?)[(3 : usize)]_?)
                ^^^? (← subbed[(3 : usize)]_?))))));
        (Rust_primitives.Hax.Folds.fold_range
          (1 : usize)
          (4 : usize)
          (fun rk _ => (do (pure true) : RustM Bool))
          rk
          (fun rk j =>
            (do
            let base : usize ← (j *? (4 : usize));
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (4 : usize)
              (fun rk _ => (do (pure true) : RustM Bool))
              rk
              (fun rk b =>
                (do
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  rk
                  round
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← rk[round]_?)
                    (← (base +? b))
                    (← ((← (← rk[(← (round -? (1 : usize)))]_?)[
                        (← (base +? b))
                        ]_?)
                      ^^^? (← (← rk[round]_?)[
                        (← ((← (base -? (4 : usize))) +? b))
                        ]_?)))))) :
                RustM (RustArray (RustArray u8 16) 11)))) :
            RustM (RustArray (RustArray u8 16) 11)))) :
        RustM (RustArray (RustArray u8 16) 11))));
  (pure rk)

--  AES SubBytes: apply S-box to all 16 bytes.
def aes_sub_bytes (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          i
          (← AES_SBOX[(← (Rust_primitives.Hax.cast_op (← state[i]_?)))]_?)) :
        RustM (RustArray u8 16))));
  (pure state)

--  AES ShiftRows: cyclic left shift of rows.
def aes_shift_rows (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let t : u8 ← state[(1 : usize)]_?;
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (1 : usize)
      (← state[(5 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (5 : usize)
      (← state[(9 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (9 : usize)
      (← state[(13 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (13 : usize)
      t);
  let t0 : u8 ← state[(2 : usize)]_?;
  let t1 : u8 ← state[(6 : usize)]_?;
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (2 : usize)
      (← state[(10 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (6 : usize)
      (← state[(14 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (10 : usize)
      t0);
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (14 : usize)
      t1);
  let t : u8 ← state[(15 : usize)]_?;
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (15 : usize)
      (← state[(11 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (11 : usize)
      (← state[(7 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (7 : usize)
      (← state[(3 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (3 : usize)
      t);
  (pure state)

--  AES MixColumns: mix each column using GF(2^8) multiplication.
def aes_mix_columns (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (4 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state col =>
        (do
        let base : usize ← (col *? (4 : usize));
        let s0 : u8 ← state[base]_?;
        let s1 : u8 ← state[(← (base +? (1 : usize)))]_?;
        let s2 : u8 ← state[(← (base +? (2 : usize)))]_?;
        let s3 : u8 ← state[(← (base +? (3 : usize)))]_?;
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            base
            (← ((← ((← ((← (gf_mul2 s0)) ^^^? (← (gf_mul3 s1)))) ^^^? s2))
              ^^^? s3)));
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (base +? (1 : usize)))
            (← ((← ((← (s0 ^^^? (← (gf_mul2 s1)))) ^^^? (← (gf_mul3 s2))))
              ^^^? s3)));
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (base +? (2 : usize)))
            (← ((← ((← (s0 ^^^? s1)) ^^^? (← (gf_mul2 s2))))
              ^^^? (← (gf_mul3 s3)))));
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (base +? (3 : usize)))
            (← ((← ((← ((← (gf_mul3 s0)) ^^^? s1)) ^^^? s2))
              ^^^? (← (gf_mul2 s3)))));
        (pure state) :
        RustM (RustArray u8 16))));
  (pure state)

--  AES AddRoundKey: XOR state with round key.
def aes_add_round_key (state : (RustArray u8 16)) (rk : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          i
          (← ((← state[i]_?) ^^^? (← rk[i]_?)))) :
        RustM (RustArray u8 16))));
  (pure state)

--  AES-128 encrypt a single 16-byte block.
-- 
--  Performs 10 rounds: initial AddRoundKey, 9 full rounds, 1 final round
--  (no MixColumns).
-- 
--  Maps to CatCrypt's `aes128_encrypt` axiom.
def aes128_encrypt (key : (RustArray u8 16)) (plaintext : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let rk : (RustArray (RustArray u8 16) 11) ← (aes128_key_expansion key);
  let state : (RustArray u8 16) := plaintext;
  let state : (RustArray u8 16) ←
    (aes_add_round_key state (← rk[(0 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      (10 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state round =>
        (do
        let state : (RustArray u8 16) ← (aes_sub_bytes state);
        let state : (RustArray u8 16) ← (aes_shift_rows state);
        let state : (RustArray u8 16) ← (aes_mix_columns state);
        let state : (RustArray u8 16) ←
          (aes_add_round_key state (← rk[round]_?));
        (pure state) :
        RustM (RustArray u8 16))));
  let state : (RustArray u8 16) ← (aes_sub_bytes state);
  let state : (RustArray u8 16) ← (aes_shift_rows state);
  let state : (RustArray u8 16) ←
    (aes_add_round_key state (← rk[(10 : usize)]_?));
  (pure state)

--  GF(2^128) constant R_b = 0^120 || 10000111 = 0x00...0087.
--  Used in the `dbl` operation for subkey derivation.
def RB : (RustArray u8 16) :=
  RustM.of_isOk
    (do
    #v[(0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (135 : u8)])
    (by rfl)

--  Doubling in GF(2^128): left-shift by 1, XOR with R_b if MSB was 1.
-- 
--  This is the core operation for CMAC subkey generation.
--  Maps to CatCrypt's GF(2^128) `dbl` operation.
def dbl (block : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let msb : u8 ← ((← block[(0 : usize)]_?) &&&? (128 : u8));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (15 : usize)
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          i
          (← (Rust_primitives.Hax.Machine_int.bitor
            (← ((← block[i]_?) <<<? (1 : i32)))
            (← ((← block[(← (i +? (1 : usize)))]_?) >>>? (7 : i32)))))) :
        RustM (RustArray u8 16))));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (15 : usize)
      (← ((← block[(15 : usize)]_?) <<<? (1 : i32))));
  let result : (RustArray u8 16) ←
    if (← (Rust_primitives.Hax.Machine_int.ne msb (0 : u8))) then
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        (16 : usize)
        (fun result _ => (do (pure true) : RustM Bool))
        result
        (fun result i =>
          (do
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← ((← result[i]_?) ^^^? (← RB[i]_?)))) :
          RustM (RustArray u8 16))))
    else
      (pure result);
  (pure result)

--  CMAC subkey generation (SP 800-38B, Section 6.1).
-- 
--  1. L = AES_K(0^128)
--  2. K1 = dbl(L)
--  3. K2 = dbl(K1)
-- 
--  Returns (K1, K2).
def cmac_subkey_gen (key : (RustArray u8 16)) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) (RustArray u8 16)) := do
  let l : (RustArray u8 16) ← (aes128_encrypt key ZERO_BLOCK);
  let k1 : (RustArray u8 16) ← (dbl l);
  let k2 : (RustArray u8 16) ← (dbl k1);
  (pure (Rust_primitives.Hax.Tuple2.mk k1 k2))

--  CMAC padding: append 1-bit then zeros to fill a block.
-- 
--  `data` contains `len` bytes (0 <= len < 16). Pads to a full 16-byte block.
def cmac_pad (data : (RustArray u8 16)) (len : usize) :
    RustM (RustArray u8 16) := do
  let padded : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let padded : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun padded _ => (do (pure true) : RustM Bool))
      padded
      (fun padded i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i len)) then
          let padded : (RustArray u8 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              padded
              i
              (← data[i]_?));
          (pure padded)
        else
          if (← (Rust_primitives.Hax.Machine_int.eq i len)) then
            let padded : (RustArray u8 16) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                padded
                i
                (128 : u8));
            (pure padded)
          else
            (pure padded) :
        RustM (RustArray u8 16))));
  (pure padded)

--  AES-CMAC computation (SP 800-38B, Section 6.2).
-- 
--  Computes CMAC-AES-128 over a message of `msg_len` bytes.
--  Message is provided in `blocks` as complete 16-byte blocks;
--  `msg_len` indicates the actual message length in bytes.
-- 
--  # Arguments
--  * `key` - 16-byte AES-128 key
--  * `blocks` - message split into 16-byte blocks (last may be partial)
--  * `num_blocks` - number of blocks used (0 for empty message)
--  * `msg_len` - total message length in bytes
-- 
--  # Returns
--  16-byte CMAC tag
-- 
--  Maps to CatCrypt's `cmac_compute`.
def cmac
    (key : (RustArray u8 16))
    (blocks : (RustArray (RustArray u8 16) 64))
    (num_blocks : usize)
    (msg_len : usize) :
    RustM (RustArray u8 16) := do
  let ⟨k1, k2⟩ ← (cmac_subkey_gen key);
  if (← (Rust_primitives.Hax.Machine_int.eq msg_len (0 : usize))) then
    let empty : (RustArray u8 16) ←
      (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
    let padded : (RustArray u8 16) ← (cmac_pad empty (0 : usize));
    let m_last : (RustArray u8 16) ← (xor_block k2 padded);
    (aes128_encrypt key m_last)
  else
    let last_block_len : usize ←
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (msg_len %? (16 : usize)))
        (0 : usize))) then
        (pure (16 : usize))
      else
        (msg_len %? (16 : usize));
    let is_complete : Bool ←
      (Rust_primitives.Hax.Machine_int.eq last_block_len (16 : usize));
    let x : (RustArray u8 16) := ZERO_BLOCK;
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun x _ => (do (pure true) : RustM Bool))
      x
      (fun x i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk Rust_primitives.Hax.Tuple0.mk x)))
        else
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            i
            (← (num_blocks -? (1 : usize))))) then
            let y : (RustArray u8 16) ← (xor_block x (← blocks[i]_?));
            let x : (RustArray u8 16) ← (aes128_encrypt key y);
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue x))
          else
            if is_complete then
              let m_last : (RustArray u8 16) ← (xor_block (← blocks[i]_?) k1);
              let y : (RustArray u8 16) ← (xor_block x m_last);
              let x : (RustArray u8 16) ← (aes128_encrypt key y);
              (pure (Core_models.Ops.Control_flow.ControlFlow.Continue x))
            else
              let padded : (RustArray u8 16) ←
                (cmac_pad (← blocks[i]_?) last_block_len);
              let m_last : (RustArray u8 16) ← (xor_block padded k2);
              let y : (RustArray u8 16) ← (xor_block x m_last);
              let x : (RustArray u8 16) ← (aes128_encrypt key y);
              (pure (Core_models.Ops.Control_flow.ControlFlow.Continue x)) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (RustArray u8 16))
          (RustArray u8 16)))))

--  Convenience: compute CMAC over a flat byte array (up to MAX_BLOCKS * 16 bytes).
-- 
--  Splits the message into 16-byte blocks and calls `cmac`.
def cmac_bytes
    (key : (RustArray u8 16))
    (msg : (RustSlice u8))
    (msg_len : usize) :
    RustM (RustArray u8 16) := do
  let blocks : (RustArray (RustArray u8 16) 64) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (64 : usize));
  let num_blocks : usize ←
    if (← (Rust_primitives.Hax.Machine_int.eq msg_len (0 : usize))) then
      (pure (0 : usize))
    else
      ((← (msg_len +? (15 : usize))) /? (16 : usize));
  let blocks : (RustArray (RustArray u8 16) 64) ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun blocks _ => (do (pure true) : RustM Bool))
      blocks
      (fun blocks i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              blocks)))
        else
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (← (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (16 : usize)
              (fun blocks _ => (do (pure true) : RustM Bool))
              blocks
              (fun blocks j =>
                (do
                let idx : usize ← ((← (i *? (16 : usize))) +? j);
                if (← (Rust_primitives.Hax.Machine_int.lt idx msg_len)) then
                  let blocks : (RustArray (RustArray u8 16) 64) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      blocks
                      i
                      (←
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                        (← blocks[i]_?)
                        j
                        (← msg[idx]_?))));
                  (pure blocks)
                else
                  (pure blocks) :
                RustM (RustArray (RustArray u8 16) 64))))))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (RustArray (RustArray u8 16) 64))
          (RustArray (RustArray u8 16) 64)))));
  (cmac key blocks num_blocks msg_len)

end Cmac_hax

