
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


namespace Aesccm_hax

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

--  Maximum message length for bounded iteration: 256 bytes.
def MAX_MSG : usize := (256 : usize)

--  Maximum AAD length for bounded iteration: 256 bytes.
def MAX_AAD : usize := (256 : usize)

--  Maximum number of CBC-MAC input blocks: B0(1) + AAD_hdr(2+256)/16 + MSG(256)/16 = 35.
--  Use 40 for safety margin.
def MAX_CBC_BLOCKS : usize := (40 : usize)

--  Maximum number of CTR blocks: ceil(256/16) + 1 = 17 for A0..A16.
def MAX_CTR_BLOCKS : usize := (18 : usize)

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
--  Produces the 44-word expanded key of FIPS 197, Section 5.2, laid out as 11 round keys.
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
--  This is the only block-cipher call CCM makes; the CBC-MAC and CTR layers are built on it.
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

--  Format the B0 block for CCM.
-- 
--  B0 = Flags || Nonce || Q
-- 
--  Flags = 64*Adata || 8*((t-2)/2) || (q-1)
--  where:
--    - Adata = 1 if there is associated data, 0 otherwise
--    - t = tag length in bytes (must be even, 4..16)
--    - q = 15 - nonce_len = number of bytes for message length encoding
--    - Q = message length encoded in q bytes (big-endian)
-- 
--  `nonce_len` must be 7..13.
def format_b0
    (nonce : (RustArray u8 13))
    (nonce_len : usize)
    (msg_len : usize)
    (tag_len : usize)
    (has_aad : usize) :
    RustM (RustArray u8 16) := do
  let b0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let q : usize ← ((15 : usize) -? nonce_len);
  let adata_flag : u8 ←
    if (← (Rust_primitives.Hax.Machine_int.ne has_aad (0 : usize))) then
      (pure (64 : u8))
    else
      (pure (0 : u8));
  let t_field : u8 ←
    ((← (Rust_primitives.Hax.cast_op
        (← ((← (tag_len -? (2 : usize))) /? (2 : usize)))))
      <<<? (3 : i32));
  let q_field : u8 ← (Rust_primitives.Hax.cast_op (← (q -? (1 : usize))));
  let b0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      b0
      (0 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← (Rust_primitives.Hax.Machine_int.bitor adata_flag t_field))
        q_field)));
  let b0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (13 : usize)
      (fun b0 _ => (do (pure true) : RustM Bool))
      b0
      (fun b0 i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i nonce_len)) then
          let b0 : (RustArray u8 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              b0
              (← ((1 : usize) +? i))
              (← nonce[i]_?));
          (pure b0)
        else
          (pure b0) :
        RustM (RustArray u8 16))));
  let len_val : usize := msg_len;
  let ⟨b0, len_val⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      q
      (fun ⟨b0, len_val⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk b0 len_val)
      (fun ⟨b0, len_val⟩ i =>
        (do
        let b0 : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            b0
            (← ((15 : usize) -? i))
            (← (Rust_primitives.Hax.cast_op (← (len_val &&&? (255 : usize))))));
        let len_val : usize ← (len_val >>>? (8 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk b0 len_val)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) usize))));
  (pure b0)

--  Format a counter block Ai for CCM-CTR mode.
-- 
--  Ai = Flags || Nonce || Counter
-- 
--  Flags = (q-1)  (lower 3 bits only)
--  Counter is q bytes, big-endian.
def format_ctr_block
    (nonce : (RustArray u8 13))
    (nonce_len : usize)
    (counter : usize) :
    RustM (RustArray u8 16) := do
  let ai : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let q : usize ← ((15 : usize) -? nonce_len);
  let ai : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      ai
      (0 : usize)
      (← (Rust_primitives.Hax.cast_op (← (q -? (1 : usize))))));
  let ai : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (13 : usize)
      (fun ai _ => (do (pure true) : RustM Bool))
      ai
      (fun ai i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i nonce_len)) then
          let ai : (RustArray u8 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              ai
              (← ((1 : usize) +? i))
              (← nonce[i]_?));
          (pure ai)
        else
          (pure ai) :
        RustM (RustArray u8 16))));
  let ctr_val : usize := counter;
  let ⟨ai, ctr_val⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      q
      (fun ⟨ai, ctr_val⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk ai ctr_val)
      (fun ⟨ai, ctr_val⟩ i =>
        (do
        let ai : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            ai
            (← ((15 : usize) -? i))
            (← (Rust_primitives.Hax.cast_op (← (ctr_val &&&? (255 : usize))))));
        let ctr_val : usize ← (ctr_val >>>? (8 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk ai ctr_val)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) usize))));
  (pure ai)

--  Increment the counter portion of a CTR block.
-- 
--  The counter occupies the last `q` bytes (big-endian).
--  q = 15 - nonce_len.
def ctr_increment (block : (RustArray u8 16)) (nonce_len : usize) :
    RustM (RustArray u8 16) := do
  let q : usize ← ((15 : usize) -? nonce_len);
  let carry : u16 := (1 : u16);
  let ⟨block, carry⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      q
      (fun ⟨block, carry⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk block carry)
      (fun ⟨block, carry⟩ i =>
        (do
        let pos : usize ← ((15 : usize) -? i);
        let sum : u16 ←
          (Core_models.Num.Impl_7.wrapping_add
            (← (Rust_primitives.Hax.cast_op (← block[pos]_?)))
            carry);
        let block : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            block
            pos
            (← (Rust_primitives.Hax.cast_op sum)));
        let carry : u16 ← (sum >>>? (8 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk block carry)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) u16))));
  (pure block)

--  Format AAD length header.
-- 
--  If 0 < a < 2^16 - 2^8: encode as 2 bytes.
--  (We only support a <= MAX_AAD = 256 which fits in 2 bytes.)
-- 
--  Returns the header bytes and number of header bytes used.
def format_aad_header (aad_len : usize) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 6) usize) := do
  let hdr : (RustArray u8 6) ←
    (Rust_primitives.Hax.repeat (0 : u8) (6 : usize));
  let hdr : (RustArray u8 6) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      hdr
      (0 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (aad_len >>>? (8 : i32))) &&&? (255 : usize))))));
  let hdr : (RustArray u8 6) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      hdr
      (1 : usize)
      (← (Rust_primitives.Hax.cast_op (← (aad_len &&&? (255 : usize))))));
  (pure (Rust_primitives.Hax.Tuple2.mk hdr (2 : usize)))

--  Compute CBC-MAC tag T for CCM.
-- 
--  Input to CBC-MAC is: B0 || [AAD header || AAD || pad] || [payload || pad]
-- 
--  Each segment is padded to a multiple of 16 bytes.
-- 
--  Returns the full 16-byte CBC-MAC tag T (before truncation/encryption).
def ccm_cbc_mac
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 13))
    (nonce_len : usize)
    (plaintext : (RustArray u8 256))
    (pt_len : usize)
    (aad : (RustArray u8 256))
    (aad_len : usize)
    (tag_len : usize) :
    RustM (RustArray u8 16) := do
  let cbc_input : (RustArray (RustArray u8 16) 40) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (40 : usize));
  let block_count : usize := (0 : usize);
  let buf : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let buf_pos : usize := (0 : usize);
  let b0 : (RustArray u8 16) ←
    (format_b0
      nonce
      nonce_len
      pt_len
      tag_len
      (← if (← (Rust_primitives.Hax.Machine_int.gt aad_len (0 : usize))) then
        (pure (1 : usize))
      else
        (pure (0 : usize))));
  let cbc_input : (RustArray (RustArray u8 16) 40) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      cbc_input
      (0 : usize)
      b0);
  let block_count : usize := (1 : usize);
  let ⟨block_count, buf, buf_pos, cbc_input⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.gt aad_len (0 : usize))) then
      let ⟨aad_hdr, hdr_len⟩ ← (format_aad_header aad_len);
      let buf : (RustArray u8 16) ←
        (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
      let buf_pos : usize := (0 : usize);
      let ⟨block_count, buf, buf_pos, cbc_input⟩ ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (6 : usize)
          (fun ⟨block_count, buf, buf_pos, cbc_input⟩ _ =>
            (do (pure true) : RustM Bool))
          (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input)
          (fun ⟨block_count, buf, buf_pos, cbc_input⟩ i =>
            (do
            if (← (Rust_primitives.Hax.Machine_int.lt i hdr_len)) then
              let buf : (RustArray u8 16) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  buf
                  buf_pos
                  (← aad_hdr[i]_?));
              let buf_pos : usize ← (buf_pos +? (1 : usize));
              if
              (← (Rust_primitives.Hax.Machine_int.eq buf_pos (16 : usize))) then
                let cbc_input : (RustArray (RustArray u8 16) 40) ←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    cbc_input
                    block_count
                    buf);
                let block_count : usize ← (block_count +? (1 : usize));
                let buf : (RustArray u8 16) ←
                  (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
                let buf_pos : usize := (0 : usize);
                (pure (Rust_primitives.Hax.Tuple4.mk
                  block_count
                  buf
                  buf_pos
                  cbc_input))
              else
                (pure (Rust_primitives.Hax.Tuple4.mk
                  block_count
                  buf
                  buf_pos
                  cbc_input))
            else
              (pure (Rust_primitives.Hax.Tuple4.mk
                block_count
                buf
                buf_pos
                cbc_input)) :
            RustM
            (Rust_primitives.Hax.Tuple4
              usize
              (RustArray u8 16)
              usize
              (RustArray (RustArray u8 16) 40)))));
      let ⟨block_count, buf, buf_pos, cbc_input⟩ ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          MAX_AAD
          (fun ⟨block_count, buf, buf_pos, cbc_input⟩ _ =>
            (do (pure true) : RustM Bool))
          (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input)
          (fun ⟨block_count, buf, buf_pos, cbc_input⟩ i =>
            (do
            if (← (Rust_primitives.Hax.Machine_int.lt i aad_len)) then
              let buf : (RustArray u8 16) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  buf
                  buf_pos
                  (← aad[i]_?));
              let buf_pos : usize ← (buf_pos +? (1 : usize));
              if
              (← (Rust_primitives.Hax.Machine_int.eq buf_pos (16 : usize))) then
                let cbc_input : (RustArray (RustArray u8 16) 40) ←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    cbc_input
                    block_count
                    buf);
                let block_count : usize ← (block_count +? (1 : usize));
                let buf : (RustArray u8 16) ←
                  (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
                let buf_pos : usize := (0 : usize);
                (pure (Rust_primitives.Hax.Tuple4.mk
                  block_count
                  buf
                  buf_pos
                  cbc_input))
              else
                (pure (Rust_primitives.Hax.Tuple4.mk
                  block_count
                  buf
                  buf_pos
                  cbc_input))
            else
              (pure (Rust_primitives.Hax.Tuple4.mk
                block_count
                buf
                buf_pos
                cbc_input)) :
            RustM
            (Rust_primitives.Hax.Tuple4
              usize
              (RustArray u8 16)
              usize
              (RustArray (RustArray u8 16) 40)))));
      if (← (Rust_primitives.Hax.Machine_int.gt buf_pos (0 : usize))) then
        let cbc_input : (RustArray (RustArray u8 16) 40) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            cbc_input
            block_count
            buf);
        let block_count : usize ← (block_count +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input))
      else
        (pure (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input))
    else
      (pure (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input));
  let ⟨block_count, buf, buf_pos, cbc_input⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.gt pt_len (0 : usize))) then
      let buf : (RustArray u8 16) ←
        (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
      let buf_pos : usize := (0 : usize);
      let ⟨block_count, buf, buf_pos, cbc_input⟩ ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          MAX_MSG
          (fun ⟨block_count, buf, buf_pos, cbc_input⟩ _ =>
            (do (pure true) : RustM Bool))
          (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input)
          (fun ⟨block_count, buf, buf_pos, cbc_input⟩ i =>
            (do
            if (← (Rust_primitives.Hax.Machine_int.lt i pt_len)) then
              let buf : (RustArray u8 16) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  buf
                  buf_pos
                  (← plaintext[i]_?));
              let buf_pos : usize ← (buf_pos +? (1 : usize));
              if
              (← (Rust_primitives.Hax.Machine_int.eq buf_pos (16 : usize))) then
                let cbc_input : (RustArray (RustArray u8 16) 40) ←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    cbc_input
                    block_count
                    buf);
                let block_count : usize ← (block_count +? (1 : usize));
                let buf : (RustArray u8 16) ←
                  (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
                let buf_pos : usize := (0 : usize);
                (pure (Rust_primitives.Hax.Tuple4.mk
                  block_count
                  buf
                  buf_pos
                  cbc_input))
              else
                (pure (Rust_primitives.Hax.Tuple4.mk
                  block_count
                  buf
                  buf_pos
                  cbc_input))
            else
              (pure (Rust_primitives.Hax.Tuple4.mk
                block_count
                buf
                buf_pos
                cbc_input)) :
            RustM
            (Rust_primitives.Hax.Tuple4
              usize
              (RustArray u8 16)
              usize
              (RustArray (RustArray u8 16) 40)))));
      if (← (Rust_primitives.Hax.Machine_int.gt buf_pos (0 : usize))) then
        let cbc_input : (RustArray (RustArray u8 16) 40) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            cbc_input
            block_count
            buf);
        let block_count : usize ← (block_count +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input))
      else
        (pure (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input))
    else
      (pure (Rust_primitives.Hax.Tuple4.mk block_count buf buf_pos cbc_input));
  let x : (RustArray u8 16) := ZERO_BLOCK;
  (Rust_primitives.Hax.Folds.fold_range_cf
    (0 : usize)
    MAX_CBC_BLOCKS
    (fun x _ => (do (pure true) : RustM Bool))
    x
    (fun x i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.ge i block_count)) then
        (pure (Core_models.Ops.Control_flow.ControlFlow.Break
          (Rust_primitives.Hax.Tuple2.mk Rust_primitives.Hax.Tuple0.mk x)))
      else
        let y : (RustArray u8 16) ← (xor_block x (← cbc_input[i]_?));
        (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
          (← (aes128_encrypt key y)))) :
      RustM
      (Core_models.Ops.Control_flow.ControlFlow
        (Rust_primitives.Hax.Tuple2
          Rust_primitives.Hax.Tuple0
          (RustArray u8 16))
        (RustArray u8 16)))))

--  CCM-AES-128 authenticated encryption.
-- 
--  # Arguments
--  * `key` - 16-byte AES-128 key
--  * `nonce` - Nonce stored in a 13-byte array (only first `nonce_len` bytes used)
--  * `nonce_len` - Actual nonce length (7..13)
--  * `plaintext` - Plaintext in a MAX_MSG-byte array
--  * `pt_len` - Actual plaintext length in bytes
--  * `aad` - Associated data in a MAX_AAD-byte array
--  * `aad_len` - Actual AAD length in bytes
--  * `tag_len` - Tag length in bytes (4, 6, 8, 10, 12, 14, or 16)
-- 
--  # Returns
--  `(ciphertext, tag)` where:
--  * `ciphertext` is a MAX_MSG-byte array (first `pt_len` bytes valid)
--  * `tag` is a 16-byte array (first `tag_len` bytes valid)
def ccm_encrypt
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 13))
    (nonce_len : usize)
    (plaintext : (RustArray u8 256))
    (pt_len : usize)
    (aad : (RustArray u8 256))
    (aad_len : usize)
    (tag_len : usize) :
    RustM
    (Rust_primitives.Hax.Tuple2 (RustArray u8 256) (RustArray u8 16))
    := do
  let t : (RustArray u8 16) ←
    (ccm_cbc_mac key nonce nonce_len plaintext pt_len aad aad_len tag_len);
  let a0 : (RustArray u8 16) ← (format_ctr_block nonce nonce_len (0 : usize));
  let s0 : (RustArray u8 16) ← (aes128_encrypt key a0);
  let tag : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let tag : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun tag _ => (do (pure true) : RustM Bool))
      tag
      (fun tag i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i tag_len)) then
          let tag : (RustArray u8 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              tag
              i
              (← ((← t[i]_?) ^^^? (← s0[i]_?))));
          (pure tag)
        else
          (pure tag) :
        RustM (RustArray u8 16))));
  let ciphertext : (RustArray u8 256) ←
    (Rust_primitives.Hax.repeat (0 : u8) (256 : usize));
  let num_pt_blocks : usize ←
    if (← (Rust_primitives.Hax.Machine_int.eq pt_len (0 : usize))) then
      (pure (0 : usize))
    else
      ((← (pt_len +? (15 : usize))) /? (16 : usize));
  let ciphertext : (RustArray u8 256) ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_CTR_BLOCKS
      (fun ciphertext _ => (do (pure true) : RustM Bool))
      ciphertext
      (fun ciphertext blk =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge blk num_pt_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              ciphertext)))
        else
          let ai : (RustArray u8 16) ←
            (format_ctr_block nonce nonce_len (← (blk +? (1 : usize))));
          let si : (RustArray u8 16) ← (aes128_encrypt key ai);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (← (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (16 : usize)
              (fun ciphertext _ => (do (pure true) : RustM Bool))
              ciphertext
              (fun ciphertext j =>
                (do
                let idx : usize ← ((← (blk *? (16 : usize))) +? j);
                if (← (Rust_primitives.Hax.Machine_int.lt idx pt_len)) then
                  let ciphertext : (RustArray u8 256) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      ciphertext
                      idx
                      (← ((← plaintext[idx]_?) ^^^? (← si[j]_?))));
                  (pure ciphertext)
                else
                  (pure ciphertext) :
                RustM (RustArray u8 256))))))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (RustArray u8 256))
          (RustArray u8 256)))));
  (pure (Rust_primitives.Hax.Tuple2.mk ciphertext tag))

--  CCM-AES-128 authenticated decryption.
-- 
--  # Arguments
--  * `key` - 16-byte AES-128 key
--  * `nonce` - Nonce stored in a 13-byte array (only first `nonce_len` bytes used)
--  * `nonce_len` - Actual nonce length (7..13)
--  * `ciphertext` - Ciphertext in a MAX_MSG-byte array
--  * `ct_len` - Actual ciphertext length in bytes
--  * `aad` - Associated data in a MAX_AAD-byte array
--  * `aad_len` - Actual AAD length in bytes
--  * `received_tag` - Received authentication tag (16-byte array, first `tag_len` bytes used)
--  * `tag_len` - Tag length in bytes (4, 6, 8, 10, 12, 14, or 16)
-- 
--  # Returns
--  `Some(plaintext)` if authentication succeeds, `None` if tag verification fails.
--  The plaintext is a MAX_MSG-byte array (first `ct_len` bytes valid).
def ccm_decrypt
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 13))
    (nonce_len : usize)
    (ciphertext : (RustArray u8 256))
    (ct_len : usize)
    (aad : (RustArray u8 256))
    (aad_len : usize)
    (received_tag : (RustArray u8 16))
    (tag_len : usize) :
    RustM (Core_models.Option.Option (RustArray u8 256)) := do
  let plaintext : (RustArray u8 256) ←
    (Rust_primitives.Hax.repeat (0 : u8) (256 : usize));
  let num_ct_blocks : usize ←
    if (← (Rust_primitives.Hax.Machine_int.eq ct_len (0 : usize))) then
      (pure (0 : usize))
    else
      ((← (ct_len +? (15 : usize))) /? (16 : usize));
  let plaintext : (RustArray u8 256) ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_CTR_BLOCKS
      (fun plaintext _ => (do (pure true) : RustM Bool))
      plaintext
      (fun plaintext blk =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge blk num_ct_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              plaintext)))
        else
          let ai : (RustArray u8 16) ←
            (format_ctr_block nonce nonce_len (← (blk +? (1 : usize))));
          let si : (RustArray u8 16) ← (aes128_encrypt key ai);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (← (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (16 : usize)
              (fun plaintext _ => (do (pure true) : RustM Bool))
              plaintext
              (fun plaintext j =>
                (do
                let idx : usize ← ((← (blk *? (16 : usize))) +? j);
                if (← (Rust_primitives.Hax.Machine_int.lt idx ct_len)) then
                  let plaintext : (RustArray u8 256) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      plaintext
                      idx
                      (← ((← ciphertext[idx]_?) ^^^? (← si[j]_?))));
                  (pure plaintext)
                else
                  (pure plaintext) :
                RustM (RustArray u8 256))))))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (RustArray u8 256))
          (RustArray u8 256)))));
  let t : (RustArray u8 16) ←
    (ccm_cbc_mac key nonce nonce_len plaintext ct_len aad aad_len tag_len);
  let a0 : (RustArray u8 16) ← (format_ctr_block nonce nonce_len (0 : usize));
  let s0 : (RustArray u8 16) ← (aes128_encrypt key a0);
  let expected_tag : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let expected_tag : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun expected_tag _ => (do (pure true) : RustM Bool))
      expected_tag
      (fun expected_tag i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i tag_len)) then
          let expected_tag : (RustArray u8 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              expected_tag
              i
              (← ((← t[i]_?) ^^^? (← s0[i]_?))));
          (pure expected_tag)
        else
          (pure expected_tag) :
        RustM (RustArray u8 16))));
  let diff : u8 := (0 : u8);
  let diff : u8 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun diff _ => (do (pure true) : RustM Bool))
      diff
      (fun diff i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i tag_len)) then
          let diff : u8 ←
            (Rust_primitives.Hax.Machine_int.bitor
              diff
              (← ((← received_tag[i]_?) ^^^? (← expected_tag[i]_?))));
          (pure diff)
        else
          (pure diff) :
        RustM u8)));
  if (← (Rust_primitives.Hax.Machine_int.eq diff (0 : u8))) then
    (pure (Core_models.Option.Option.Some plaintext))
  else
    (pure Core_models.Option.Option.None)

end Aesccm_hax

