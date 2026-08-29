
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


namespace Ctrdrbg_hax

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

--  Seed length for AES-128 CTR_DRBG: keylen + blocklen = 32 bytes.
def SEEDLEN : usize := (32 : usize)

--  Maximum number of blocks that can be generated in a single call.
def MAX_GEN_BLOCKS : usize := (16 : usize)

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

--  CTR_DRBG internal state: Key and V (counter).
structure CtrDrbgState where
  key : (RustArray u8 16)
  v : (RustArray u8 16)

@[instance] opaque Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes CtrDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  Core_models.Clone.Clone CtrDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes CtrDrbgState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Marker.Copy CtrDrbgState :=
  by constructor <;> exact Inhabited.default

--  Increment a 128-bit big-endian counter by 1, wrapping on overflow.
-- 
--  Treats the 16-byte array as a big-endian 128-bit integer and adds 1.
--  On overflow (0xFF...FF + 1), wraps to 0x00...00.
def increment_counter (v : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) := v;
  let carry : u16 := (1 : u16);
  let ⟨carry, result⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun ⟨carry, result⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk carry result)
      (fun ⟨carry, result⟩ i =>
        (do
        let idx : usize ← ((15 : usize) -? i);
        let sum : u16 ←
          ((← (Rust_primitives.Hax.cast_op (← result[idx]_?))) +? carry);
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            idx
            (← (Rust_primitives.Hax.cast_op sum)));
        let carry : u16 ← (sum >>>? (8 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk carry result)) :
        RustM (Rust_primitives.Hax.Tuple2 u16 (RustArray u8 16)))));
  (pure result)

--  CTR_DRBG Update function (SP 800-90A, Section 10.2.1.2).
-- 
--  Refreshes the DRBG state using provided_data (seedlen = 32 bytes).
--  For AES-128, seedlen = 32 bytes, so we need exactly 2 AES blocks.
-- 
--  Algorithm:
--    temp = empty
--    while len(temp) < seedlen:
--      V = (V + 1) mod 2^128
--      output_block = AES_Key(V)
--      temp = temp || output_block
--    temp = temp[0..seedlen]
--    temp = temp XOR provided_data
--    Key = temp[0..16]
--    V = temp[16..32]
--    return (Key, V)
def ctr_drbg_update (state : CtrDrbgState) (provided_data : (RustArray u8 32)) :
    RustM CtrDrbgState := do
  let v : (RustArray u8 16) := (CtrDrbgState.v state);
  let temp : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let ⟨temp, v⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (2 : usize)
      (fun ⟨temp, v⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk temp v)
      (fun ⟨temp, v⟩ i =>
        (do
        let v : (RustArray u8 16) ← (increment_counter v);
        let output_block : (RustArray u8 16) ←
          (aes128_encrypt (CtrDrbgState.key state) v);
        let temp : (RustArray u8 32) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (16 : usize)
            (fun temp _ => (do (pure true) : RustM Bool))
            temp
            (fun temp j =>
              (do
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                temp
                (← ((← (i *? (16 : usize))) +? j))
                (← output_block[j]_?)) :
              RustM (RustArray u8 32))));
        (pure (Rust_primitives.Hax.Tuple2.mk temp v)) :
        RustM
        (Rust_primitives.Hax.Tuple2 (RustArray u8 32) (RustArray u8 16)))));
  let temp : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun temp _ => (do (pure true) : RustM Bool))
      temp
      (fun temp i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          temp
          i
          (← ((← temp[i]_?) ^^^? (← provided_data[i]_?)))) :
        RustM (RustArray u8 32))));
  let new_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let new_v : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let ⟨new_key, new_v⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun ⟨new_key, new_v⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk new_key new_v)
      (fun ⟨new_key, new_v⟩ i =>
        (do
        let new_key : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            new_key
            i
            (← temp[i]_?));
        let new_v : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            new_v
            i
            (← temp[(← ((16 : usize) +? i))]_?));
        (pure (Rust_primitives.Hax.Tuple2.mk new_key new_v)) :
        RustM
        (Rust_primitives.Hax.Tuple2 (RustArray u8 16) (RustArray u8 16)))));
  (pure (CtrDrbgState.mk (key := new_key) (v := new_v)))

--  CTR_DRBG Instantiate function (SP 800-90A, Section 10.2.1.3).
-- 
--  Initializes a new DRBG state from entropy input and personalization string.
--  Both inputs are seedlen = 32 bytes. If personalization is shorter, it should
--  be zero-padded by the caller.
-- 
--  Algorithm:
--    Key = 0x00 * 16
--    V = 0x00 * 16
--    seed_material = entropy XOR personalization
--    (Key, V) = Update(seed_material, Key, V)
--    return (Key, V)
def ctr_drbg_instantiate
    (entropy : (RustArray u8 32))
    (personalization : (RustArray u8 32)) :
    RustM CtrDrbgState := do
  let initial_state : CtrDrbgState :=
    (CtrDrbgState.mk
      (key := (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize))))
      (v := (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))));
  let seed_material : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let seed_material : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          seed_material
          i
          (← ((← entropy[i]_?) ^^^? (← personalization[i]_?)))) :
        RustM (RustArray u8 32))));
  (ctr_drbg_update initial_state seed_material)

--  CTR_DRBG Generate function (SP 800-90A, Section 10.2.1.5).
-- 
--  Generates pseudorandom output blocks and updates the state.
--  `num_blocks` specifies how many 16-byte blocks to generate (capped at MAX_GEN_BLOCKS).
--  `additional_input` is optional additional data (32 bytes, use zeros if none).
-- 
--  Algorithm:
--    For i in 0..num_blocks:
--      V = (V + 1) mod 2^128
--      output_block[i] = AES_Key(V)
--    (Key, V) = Update(additional_input, Key, V)
--    return (output_blocks, (Key, V))
-- 
--  Returns (new_state, output_blocks).
def ctr_drbg_generate
    (state : CtrDrbgState)
    (num_blocks : usize)
    (additional_input : (RustArray u8 32)) :
    RustM
    (Rust_primitives.Hax.Tuple2 CtrDrbgState (RustArray (RustArray u8 16) 16))
    := do
  let v : (RustArray u8 16) := (CtrDrbgState.v state);
  let output : (RustArray (RustArray u8 16) 16) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (16 : usize));
  let ⟨output, v⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_GEN_BLOCKS
      (fun ⟨output, v⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk output v)
      (fun ⟨output, v⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk output v))))
        else
          let v : (RustArray u8 16) ← (increment_counter v);
          let output : (RustArray (RustArray u8 16) 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              output
              i
              (← (aes128_encrypt (CtrDrbgState.key state) v)));
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk output v))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2
              (RustArray (RustArray u8 16) 16)
              (RustArray u8 16)))
          (Rust_primitives.Hax.Tuple2
            (RustArray (RustArray u8 16) 16)
            (RustArray u8 16))))));
  let gen_state : CtrDrbgState :=
    (CtrDrbgState.mk (key := (CtrDrbgState.key state)) (v := v));
  let new_state : CtrDrbgState ← (ctr_drbg_update gen_state additional_input);
  (pure (Rust_primitives.Hax.Tuple2.mk new_state output))

--  CTR_DRBG Reseed function (SP 800-90A, Section 10.2.1.4).
-- 
--  Reseeds the DRBG with new entropy and optional additional input.
-- 
--  Algorithm:
--    seed_material = entropy XOR additional_input
--    (Key, V) = Update(seed_material, Key, V)
--    return (Key, V)
def ctr_drbg_reseed
    (state : CtrDrbgState)
    (entropy : (RustArray u8 32))
    (additional_input : (RustArray u8 32)) :
    RustM CtrDrbgState := do
  let seed_material : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let seed_material : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      SEEDLEN
      (fun seed_material _ => (do (pure true) : RustM Bool))
      seed_material
      (fun seed_material i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          seed_material
          i
          (← ((← entropy[i]_?) ^^^? (← additional_input[i]_?)))) :
        RustM (RustArray u8 32))));
  (ctr_drbg_update state seed_material)

end Ctrdrbg_hax

