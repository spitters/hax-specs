
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


namespace Xtsaes_hax

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

--  AES inverse S-box lookup table (FIPS 197, Figure 14).
def AES_INV_SBOX : (RustArray u8 256) :=
  RustM.of_isOk
    (do
    #v[(82 : u8),
         (9 : u8),
         (106 : u8),
         (213 : u8),
         (48 : u8),
         (54 : u8),
         (165 : u8),
         (56 : u8),
         (191 : u8),
         (64 : u8),
         (163 : u8),
         (158 : u8),
         (129 : u8),
         (243 : u8),
         (215 : u8),
         (251 : u8),
         (124 : u8),
         (227 : u8),
         (57 : u8),
         (130 : u8),
         (155 : u8),
         (47 : u8),
         (255 : u8),
         (135 : u8),
         (52 : u8),
         (142 : u8),
         (67 : u8),
         (68 : u8),
         (196 : u8),
         (222 : u8),
         (233 : u8),
         (203 : u8),
         (84 : u8),
         (123 : u8),
         (148 : u8),
         (50 : u8),
         (166 : u8),
         (194 : u8),
         (35 : u8),
         (61 : u8),
         (238 : u8),
         (76 : u8),
         (149 : u8),
         (11 : u8),
         (66 : u8),
         (250 : u8),
         (195 : u8),
         (78 : u8),
         (8 : u8),
         (46 : u8),
         (161 : u8),
         (102 : u8),
         (40 : u8),
         (217 : u8),
         (36 : u8),
         (178 : u8),
         (118 : u8),
         (91 : u8),
         (162 : u8),
         (73 : u8),
         (109 : u8),
         (139 : u8),
         (209 : u8),
         (37 : u8),
         (114 : u8),
         (248 : u8),
         (246 : u8),
         (100 : u8),
         (134 : u8),
         (104 : u8),
         (152 : u8),
         (22 : u8),
         (212 : u8),
         (164 : u8),
         (92 : u8),
         (204 : u8),
         (93 : u8),
         (101 : u8),
         (182 : u8),
         (146 : u8),
         (108 : u8),
         (112 : u8),
         (72 : u8),
         (80 : u8),
         (253 : u8),
         (237 : u8),
         (185 : u8),
         (218 : u8),
         (94 : u8),
         (21 : u8),
         (70 : u8),
         (87 : u8),
         (167 : u8),
         (141 : u8),
         (157 : u8),
         (132 : u8),
         (144 : u8),
         (216 : u8),
         (171 : u8),
         (0 : u8),
         (140 : u8),
         (188 : u8),
         (211 : u8),
         (10 : u8),
         (247 : u8),
         (228 : u8),
         (88 : u8),
         (5 : u8),
         (184 : u8),
         (179 : u8),
         (69 : u8),
         (6 : u8),
         (208 : u8),
         (44 : u8),
         (30 : u8),
         (143 : u8),
         (202 : u8),
         (63 : u8),
         (15 : u8),
         (2 : u8),
         (193 : u8),
         (175 : u8),
         (189 : u8),
         (3 : u8),
         (1 : u8),
         (19 : u8),
         (138 : u8),
         (107 : u8),
         (58 : u8),
         (145 : u8),
         (17 : u8),
         (65 : u8),
         (79 : u8),
         (103 : u8),
         (220 : u8),
         (234 : u8),
         (151 : u8),
         (242 : u8),
         (207 : u8),
         (206 : u8),
         (240 : u8),
         (180 : u8),
         (230 : u8),
         (115 : u8),
         (150 : u8),
         (172 : u8),
         (116 : u8),
         (34 : u8),
         (231 : u8),
         (173 : u8),
         (53 : u8),
         (133 : u8),
         (226 : u8),
         (249 : u8),
         (55 : u8),
         (232 : u8),
         (28 : u8),
         (117 : u8),
         (223 : u8),
         (110 : u8),
         (71 : u8),
         (241 : u8),
         (26 : u8),
         (113 : u8),
         (29 : u8),
         (41 : u8),
         (197 : u8),
         (137 : u8),
         (111 : u8),
         (183 : u8),
         (98 : u8),
         (14 : u8),
         (170 : u8),
         (24 : u8),
         (190 : u8),
         (27 : u8),
         (252 : u8),
         (86 : u8),
         (62 : u8),
         (75 : u8),
         (198 : u8),
         (210 : u8),
         (121 : u8),
         (32 : u8),
         (154 : u8),
         (219 : u8),
         (192 : u8),
         (254 : u8),
         (120 : u8),
         (205 : u8),
         (90 : u8),
         (244 : u8),
         (31 : u8),
         (221 : u8),
         (168 : u8),
         (51 : u8),
         (136 : u8),
         (7 : u8),
         (199 : u8),
         (49 : u8),
         (177 : u8),
         (18 : u8),
         (16 : u8),
         (89 : u8),
         (39 : u8),
         (128 : u8),
         (236 : u8),
         (95 : u8),
         (96 : u8),
         (81 : u8),
         (127 : u8),
         (169 : u8),
         (25 : u8),
         (181 : u8),
         (74 : u8),
         (13 : u8),
         (45 : u8),
         (229 : u8),
         (122 : u8),
         (159 : u8),
         (147 : u8),
         (201 : u8),
         (156 : u8),
         (239 : u8),
         (160 : u8),
         (224 : u8),
         (59 : u8),
         (77 : u8),
         (174 : u8),
         (42 : u8),
         (245 : u8),
         (176 : u8),
         (200 : u8),
         (235 : u8),
         (187 : u8),
         (60 : u8),
         (131 : u8),
         (83 : u8),
         (153 : u8),
         (97 : u8),
         (23 : u8),
         (43 : u8),
         (4 : u8),
         (126 : u8),
         (186 : u8),
         (119 : u8),
         (214 : u8),
         (38 : u8),
         (225 : u8),
         (105 : u8),
         (20 : u8),
         (99 : u8),
         (85 : u8),
         (33 : u8),
         (12 : u8),
         (125 : u8)])
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

--  Maximum number of 16-byte blocks per sector (32 blocks = 512 bytes).
def MAX_BLOCKS : usize := (32 : usize)

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

--  Multiply by 9 in GF(2^8): 9*x = 8*x XOR x.
def gf_mul9 (x : u8) : RustM u8 := do
  ((← (gf_mul2 (← (gf_mul2 (← (gf_mul2 x)))))) ^^^? x)

--  Multiply by 11 in GF(2^8): 11*x = 8*x XOR 2*x XOR x.
def gf_mul11 (x : u8) : RustM u8 := do
  ((← ((← (gf_mul2 (← (gf_mul2 (← (gf_mul2 x)))))) ^^^? (← (gf_mul2 x))))
    ^^^? x)

--  Multiply by 13 in GF(2^8): 13*x = 8*x XOR 4*x XOR x.
def gf_mul13 (x : u8) : RustM u8 := do
  ((← ((← (gf_mul2 (← (gf_mul2 (← (gf_mul2 x))))))
      ^^^? (← (gf_mul2 (← (gf_mul2 x))))))
    ^^^? x)

--  Multiply by 14 in GF(2^8): 14*x = 8*x XOR 4*x XOR 2*x.
def gf_mul14 (x : u8) : RustM u8 := do
  ((← ((← (gf_mul2 (← (gf_mul2 (← (gf_mul2 x))))))
      ^^^? (← (gf_mul2 (← (gf_mul2 x))))))
    ^^^? (← (gf_mul2 x)))

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

--  AES InvSubBytes: apply inverse S-box to all 16 bytes.
def aes_inv_sub_bytes (state : (RustArray u8 16)) :
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
          (← AES_INV_SBOX[(← (Rust_primitives.Hax.cast_op (← state[i]_?)))]_?))
        :
        RustM (RustArray u8 16))));
  (pure state)

--  AES InvShiftRows: cyclic right shift of rows.
def aes_inv_shift_rows (state : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let t : u8 ← state[(13 : usize)]_?;
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (13 : usize)
      (← state[(9 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (9 : usize)
      (← state[(5 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (5 : usize)
      (← state[(1 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (1 : usize)
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
  let t : u8 ← state[(3 : usize)]_?;
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (3 : usize)
      (← state[(7 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (7 : usize)
      (← state[(11 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (11 : usize)
      (← state[(15 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (15 : usize)
      t);
  (pure state)

--  AES InvMixColumns: inverse mix each column using GF(2^8) multiplication.
def aes_inv_mix_columns (state : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
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
            (← ((← ((← ((← (gf_mul14 s0)) ^^^? (← (gf_mul11 s1))))
                ^^^? (← (gf_mul13 s2))))
              ^^^? (← (gf_mul9 s3)))));
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (base +? (1 : usize)))
            (← ((← ((← ((← (gf_mul9 s0)) ^^^? (← (gf_mul14 s1))))
                ^^^? (← (gf_mul11 s2))))
              ^^^? (← (gf_mul13 s3)))));
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (base +? (2 : usize)))
            (← ((← ((← ((← (gf_mul13 s0)) ^^^? (← (gf_mul9 s1))))
                ^^^? (← (gf_mul14 s2))))
              ^^^? (← (gf_mul11 s3)))));
        let state : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            (← (base +? (3 : usize)))
            (← ((← ((← ((← (gf_mul11 s0)) ^^^? (← (gf_mul13 s1))))
                ^^^? (← (gf_mul9 s2))))
              ^^^? (← (gf_mul14 s3)))));
        (pure state) :
        RustM (RustArray u8 16))));
  (pure state)

--  AES-128 decrypt a single 16-byte block.
-- 
--  Performs 10 inverse rounds: initial AddRoundKey(10), 9 full inverse rounds,
--  1 final inverse round.
-- 
--  Maps to CatCrypt's `aes128_decrypt` axiom.
def aes128_decrypt (key : (RustArray u8 16)) (ciphertext : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let rk : (RustArray (RustArray u8 16) 11) ← (aes128_key_expansion key);
  let state : (RustArray u8 16) := ciphertext;
  let state : (RustArray u8 16) ←
    (aes_add_round_key state (← rk[(10 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Core_models.Iter.Traits.Iterator.Iterator.fold
      (← (Core_models.Iter.Traits.Collect.IntoIterator.into_iter
        (Core_models.Iter.Adapters.Rev.Rev (Core_models.Ops.Range.Range usize))
        (← (Core_models.Iter.Traits.Iterator.Iterator.rev
          (Core_models.Ops.Range.Range usize)
          (Core_models.Ops.Range.Range.mk
            (start := (1 : usize))
            (_end := (10 : usize)))))))
      state
      (fun state round =>
        (do
        let state : (RustArray u8 16) ← (aes_inv_shift_rows state);
        let state : (RustArray u8 16) ← (aes_inv_sub_bytes state);
        let state : (RustArray u8 16) ←
          (aes_add_round_key state (← rk[round]_?));
        let state : (RustArray u8 16) ← (aes_inv_mix_columns state);
        (pure state) :
        RustM (RustArray u8 16))));
  let state : (RustArray u8 16) ← (aes_inv_shift_rows state);
  let state : (RustArray u8 16) ← (aes_inv_sub_bytes state);
  let state : (RustArray u8 16) ←
    (aes_add_round_key state (← rk[(0 : usize)]_?));
  (pure state)

--  Multiply a tweak value by alpha in GF(2^128) with polynomial
--  x^128 + x^7 + x^2 + x + 1.
-- 
--  XTS uses little-endian bit ordering:
--  - The tweak is treated as a 128-bit little-endian integer
--  - Multiplication by alpha = left shift of the LE integer
--  - Byte 0 is least significant, byte 15 is most significant
--  - If bit 127 (byte[15] bit 7) was set, XOR 0x87 into byte[0]
-- 
--  Concretely:
--    carry_out = (tweak[15] >> 7) & 1
--    for i in (1..16).rev(): result[i] = (tweak[i] << 1) | (tweak[i-1] >> 7)
--    result[0] = (tweak[0] << 1) ^ (carry_out * 0x87)
-- 
--  Maps to CatCrypt's GF(2^128) `mul_alpha` operation for XTS.
def gf128_mul_alpha (tweak : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let carry_out : u8 ←
    ((← ((← tweak[(15 : usize)]_?) >>>? (7 : i32))) &&&? (1 : u8));
  let result : (RustArray u8 16) ←
    (Core_models.Iter.Traits.Iterator.Iterator.fold
      (← (Core_models.Iter.Traits.Collect.IntoIterator.into_iter
        (Core_models.Iter.Adapters.Rev.Rev (Core_models.Ops.Range.Range usize))
        (← (Core_models.Iter.Traits.Iterator.Iterator.rev
          (Core_models.Ops.Range.Range usize)
          (Core_models.Ops.Range.Range.mk
            (start := (1 : usize))
            (_end := (16 : usize)))))))
      result
      (fun result i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          i
          (← (Rust_primitives.Hax.Machine_int.bitor
            (← ((← tweak[i]_?) <<<? (1 : i32)))
            (← ((← tweak[(← (i -? (1 : usize)))]_?) >>>? (7 : i32)))))) :
        RustM (RustArray u8 16))));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (0 : usize)
      (← ((← ((← tweak[(0 : usize)]_?) <<<? (1 : i32)))
        ^^^? (← (Core_models.Num.Impl_6.wrapping_mul carry_out (135 : u8))))));
  (pure result)

--  Encrypt a single 16-byte block using XTS-AES.
-- 
--  # Arguments
--  * `key1` - AES key for data encryption
--  * `key2` - AES key for tweak encryption
--  * `tweak_input` - 16-byte tweak (typically sector number in LE)
--  * `block_index` - block index within the data unit (for alpha multiplication)
--  * `plaintext` - 16-byte plaintext block
-- 
--  # Returns
--  16-byte ciphertext block
-- 
--  Algorithm:
--    T = AES_K2(tweak_input) then multiply by alpha `block_index` times
--    PP = plaintext XOR T
--    CC = AES_K1(PP)
--    ciphertext = CC XOR T
def xts_encrypt_block
    (key1 : (RustArray u8 16))
    (key2 : (RustArray u8 16))
    (tweak_input : (RustArray u8 16))
    (block_index : usize)
    (plaintext : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let tweak : (RustArray u8 16) ← (aes128_encrypt key2 tweak_input);
  let tweak : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun tweak _ => (do (pure true) : RustM Bool))
      tweak
      (fun tweak i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i block_index)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              tweak)))
        else
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (← (gf128_mul_alpha tweak)))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (RustArray u8 16))
          (RustArray u8 16)))));
  let pp : (RustArray u8 16) ← (xor_block plaintext tweak);
  let cc : (RustArray u8 16) ← (aes128_encrypt key1 pp);
  (xor_block cc tweak)

--  Decrypt a single 16-byte block using XTS-AES.
-- 
--  # Arguments
--  * `key1` - AES key for data encryption/decryption
--  * `key2` - AES key for tweak encryption
--  * `tweak_input` - 16-byte tweak (typically sector number in LE)
--  * `block_index` - block index within the data unit (for alpha multiplication)
--  * `ciphertext` - 16-byte ciphertext block
-- 
--  # Returns
--  16-byte plaintext block
-- 
--  Algorithm:
--    T = AES_K2(tweak_input) then multiply by alpha `block_index` times
--    CC = ciphertext XOR T
--    PP = AES_K1_decrypt(CC)
--    plaintext = PP XOR T
def xts_decrypt_block
    (key1 : (RustArray u8 16))
    (key2 : (RustArray u8 16))
    (tweak_input : (RustArray u8 16))
    (block_index : usize)
    (ciphertext : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let tweak : (RustArray u8 16) ← (aes128_encrypt key2 tweak_input);
  let tweak : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun tweak _ => (do (pure true) : RustM Bool))
      tweak
      (fun tweak i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i block_index)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              tweak)))
        else
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (← (gf128_mul_alpha tweak)))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (RustArray u8 16))
          (RustArray u8 16)))));
  let cc : (RustArray u8 16) ← (xor_block ciphertext tweak);
  let pp : (RustArray u8 16) ← (aes128_decrypt key1 cc);
  (xor_block pp tweak)

--  Encrypt a full sector (sequence of 16-byte blocks) using XTS-AES.
-- 
--  # Arguments
--  * `key1` - AES key for data encryption
--  * `key2` - AES key for tweak encryption
--  * `tweak_input` - 16-byte tweak (sector number encoded as LE 128-bit)
--  * `data_blocks` - array of plaintext blocks (up to MAX_BLOCKS)
--  * `num_blocks` - number of blocks to encrypt (1..=MAX_BLOCKS)
-- 
--  # Returns
--  Array of encrypted blocks (same size as input)
-- 
--  Maps to CatCrypt's `xts_encrypt_sector`.
def xts_encrypt_sector
    (key1 : (RustArray u8 16))
    (key2 : (RustArray u8 16))
    (tweak_input : (RustArray u8 16))
    (data_blocks : (RustArray (RustArray u8 16) 32))
    (num_blocks : usize) :
    RustM (RustArray (RustArray u8 16) 32) := do
  let result : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let tweak : (RustArray u8 16) ← (aes128_encrypt key2 tweak_input);
  let ⟨result, tweak⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun ⟨result, tweak⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk result tweak)
      (fun ⟨result, tweak⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk result tweak))))
        else
          let pp : (RustArray u8 16) ← (xor_block (← data_blocks[i]_?) tweak);
          let cc : (RustArray u8 16) ← (aes128_encrypt key1 pp);
          let result : (RustArray (RustArray u8 16) 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              result
              i
              (← (xor_block cc tweak)));
          let tweak : (RustArray u8 16) ← (gf128_mul_alpha tweak);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk result tweak))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2
              (RustArray (RustArray u8 16) 32)
              (RustArray u8 16)))
          (Rust_primitives.Hax.Tuple2
            (RustArray (RustArray u8 16) 32)
            (RustArray u8 16))))));
  (pure result)

--  Decrypt a full sector (sequence of 16-byte blocks) using XTS-AES.
-- 
--  # Arguments
--  * `key1` - AES key for data decryption
--  * `key2` - AES key for tweak encryption
--  * `tweak_input` - 16-byte tweak (sector number encoded as LE 128-bit)
--  * `data_blocks` - array of ciphertext blocks (up to MAX_BLOCKS)
--  * `num_blocks` - number of blocks to decrypt (1..=MAX_BLOCKS)
-- 
--  # Returns
--  Array of decrypted blocks (same size as input)
-- 
--  Maps to CatCrypt's `xts_decrypt_sector`.
def xts_decrypt_sector
    (key1 : (RustArray u8 16))
    (key2 : (RustArray u8 16))
    (tweak_input : (RustArray u8 16))
    (data_blocks : (RustArray (RustArray u8 16) 32))
    (num_blocks : usize) :
    RustM (RustArray (RustArray u8 16) 32) := do
  let result : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let tweak : (RustArray u8 16) ← (aes128_encrypt key2 tweak_input);
  let ⟨result, tweak⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun ⟨result, tweak⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk result tweak)
      (fun ⟨result, tweak⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk result tweak))))
        else
          let cc : (RustArray u8 16) ← (xor_block (← data_blocks[i]_?) tweak);
          let pp : (RustArray u8 16) ← (aes128_decrypt key1 cc);
          let result : (RustArray (RustArray u8 16) 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              result
              i
              (← (xor_block pp tweak)));
          let tweak : (RustArray u8 16) ← (gf128_mul_alpha tweak);
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk result tweak))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2
              (RustArray (RustArray u8 16) 32)
              (RustArray u8 16)))
          (Rust_primitives.Hax.Tuple2
            (RustArray (RustArray u8 16) 32)
            (RustArray u8 16))))));
  (pure result)

--  Convenience: encode a 64-bit sector number as a 16-byte LE tweak block.
-- 
--  The sector number is placed in the first 8 bytes in little-endian order;
--  the remaining 8 bytes are zero.
def sector_number_to_tweak (sector_number : u64) : RustM (RustArray u8 16) := do
  let tweak : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let bytes : (RustArray u8 8) ←
    (Core_models.Num.Impl_9.to_le_bytes sector_number);
  let tweak : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun tweak _ => (do (pure true) : RustM Bool))
      tweak
      (fun tweak i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          tweak
          i
          (← bytes[i]_?)) :
        RustM (RustArray u8 16))));
  (pure tweak)

end Xtsaes_hax

