
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


namespace Aesgcmsiv_hax

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

abbrev Block : Type := (RustArray u8 16)

abbrev AesKey : Type := (RustArray u8 16)

abbrev RoundKeys : Type := (RustArray (RustArray u8 16) 11)

abbrev Nonce : Type := (RustArray u8 12)

def ZERO_BLOCK : (RustArray u8 16) :=
  RustM.of_isOk (do (Rust_primitives.Hax.repeat (0 : u8) (16 : usize))) (by rfl)

def MAX_BLOCKS : usize := (32 : usize)

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

def gf_mul2 (x : u8) : RustM u8 := do
  let s : u16 ← ((← (Rust_primitives.Hax.cast_op x)) <<<? (1 : i32));
  (Rust_primitives.Hax.cast_op
    (← if
    (← (Rust_primitives.Hax.Machine_int.ne (← (x &&&? (128 : u8))) (0 : u8)))
    then
      (s ^^^? (27 : u16))
    else
      (pure s)))

def gf_mul3 (x : u8) : RustM u8 := do ((← (gf_mul2 x)) ^^^? x)

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

def rot_word (w : (RustArray u8 4)) : RustM (RustArray u8 4) := do
  (pure #v[(← w[(1 : usize)]_?),
             (← w[(2 : usize)]_?),
             (← w[(3 : usize)]_?),
             (← w[(0 : usize)]_?)])

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
        let subbed : (RustArray u8 4) ← (sub_word (← (rot_word prev_last)));
        let rc : u8 ← RCON[(← (round -? (1 : usize)))]_?;
        let rk : (RustArray (RustArray u8 16) 11) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            rk
            round
            (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              (← rk[round]_?)
              (0 : usize)
              (← ((← ((← (← rk[(← (round -? (1 : usize)))]_?)[(0 : usize)]_?)
                  ^^^? (← subbed[(0 : usize)]_?)))
                ^^^? rc)))));
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

def aes_sub_bytes (s : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          s
          i
          (← AES_SBOX[(← (Rust_primitives.Hax.cast_op (← s[i]_?)))]_?)) :
        RustM (RustArray u8 16))));
  (pure s)

def aes_shift_rows (s : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let t : u8 ← s[(1 : usize)]_?;
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (1 : usize)
      (← s[(5 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (5 : usize)
      (← s[(9 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (9 : usize)
      (← s[(13 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (13 : usize)
      t);
  let t0 : u8 ← s[(2 : usize)]_?;
  let t1 : u8 ← s[(6 : usize)]_?;
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (2 : usize)
      (← s[(10 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (6 : usize)
      (← s[(14 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (10 : usize)
      t0);
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (14 : usize)
      t1);
  let t : u8 ← s[(15 : usize)]_?;
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (15 : usize)
      (← s[(11 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (11 : usize)
      (← s[(7 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (7 : usize)
      (← s[(3 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (3 : usize)
      t);
  (pure s)

def aes_mix_columns (s : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (4 : usize)
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s col =>
        (do
        let b : usize ← (col *? (4 : usize));
        let ⟨s0, s1, s2, s3⟩ :=
          (Rust_primitives.Hax.Tuple4.mk
            (← s[b]_?)
            (← s[(← (b +? (1 : usize)))]_?)
            (← s[(← (b +? (2 : usize)))]_?)
            (← s[(← (b +? (3 : usize)))]_?));
        let s : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            s
            b
            (← ((← ((← ((← (gf_mul2 s0)) ^^^? (← (gf_mul3 s1)))) ^^^? s2))
              ^^^? s3)));
        let s : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            s
            (← (b +? (1 : usize)))
            (← ((← ((← (s0 ^^^? (← (gf_mul2 s1)))) ^^^? (← (gf_mul3 s2))))
              ^^^? s3)));
        let s : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            s
            (← (b +? (2 : usize)))
            (← ((← ((← (s0 ^^^? s1)) ^^^? (← (gf_mul2 s2))))
              ^^^? (← (gf_mul3 s3)))));
        let s : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            s
            (← (b +? (3 : usize)))
            (← ((← ((← ((← (gf_mul3 s0)) ^^^? s1)) ^^^? s2))
              ^^^? (← (gf_mul2 s3)))));
        (pure s) :
        RustM (RustArray u8 16))));
  (pure s)

def aes_add_round_key (s : (RustArray u8 16)) (rk : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          s
          i
          (← ((← s[i]_?) ^^^? (← rk[i]_?)))) :
        RustM (RustArray u8 16))));
  (pure s)

def aes128_encrypt (key : (RustArray u8 16)) (pt : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let rk : (RustArray (RustArray u8 16) 11) ← (aes128_key_expansion key);
  let s : (RustArray u8 16) := pt;
  let s : (RustArray u8 16) ← (aes_add_round_key s (← rk[(0 : usize)]_?));
  let s : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      (10 : usize)
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s round =>
        (do
        let s : (RustArray u8 16) ← (aes_sub_bytes s);
        let s : (RustArray u8 16) ← (aes_shift_rows s);
        let s : (RustArray u8 16) ← (aes_mix_columns s);
        let s : (RustArray u8 16) ← (aes_add_round_key s (← rk[round]_?));
        (pure s) :
        RustM (RustArray u8 16))));
  let s : (RustArray u8 16) ← (aes_sub_bytes s);
  let s : (RustArray u8 16) ← (aes_shift_rows s);
  let s : (RustArray u8 16) ← (aes_add_round_key s (← rk[(10 : usize)]_?));
  (pure s)

def le_u64 (bytes : (RustSlice u8)) (offset : usize) : RustM u64 := do
  let v : u64 := (0 : u64);
  let v : u64 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun v _ => (do (pure true) : RustM Bool))
      v
      (fun v i =>
        (do
        (Rust_primitives.Hax.Machine_int.bitor
          v
          (← ((← (Rust_primitives.Hax.cast_op (← bytes[(← (offset +? i))]_?)))
            <<<? (← (i *? (8 : usize)))))) :
        RustM u64)));
  (pure v)

def put_le_u64 (bytes : (RustSlice u8)) (offset : usize) (v : u64) :
    RustM (RustSlice u8) := do
  let bytes : (RustSlice u8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun bytes _ => (do (pure true) : RustM Bool))
      bytes
      (fun bytes i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          bytes
          (← (offset +? i))
          (← (Rust_primitives.Hax.cast_op
            (← ((← (v >>>? (← (i *? (8 : usize))))) &&&? (255 : u64)))))) :
        RustM (RustSlice u8))));
  (pure bytes)

--  Reduction constant: q(x) = x^127 + x^126 + x^121 + 1 (= p(x) - x^128).
--  As (lo, hi) in LE u64: q_lo = 1, q_hi = 0xc200000000000000.
def Q_LO : u64 := (1 : u64)

def Q_HI : u64 := (13979173243358019584 : u64)

--  Multiply by x in GF(2^128): left shift by 1 with conditional reduction.
def gf128_mul_x (lo : u64) (hi : u64) :
    RustM (Rust_primitives.Hax.Tuple2 u64 u64) := do
  let msb : u64 ← ((← (hi >>>? (63 : i32))) &&&? (1 : u64));
  let hi : u64 ←
    (Rust_primitives.Hax.Machine_int.bitor
      (← (hi <<<? (1 : i32)))
      (← (lo >>>? (63 : i32))));
  let lo : u64 ← (lo <<<? (1 : i32));
  let ⟨hi, lo⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.eq msb (1 : u64))) then
      let lo : u64 ← (lo ^^^? Q_LO);
      let hi : u64 ← (hi ^^^? Q_HI);
      (pure (Rust_primitives.Hax.Tuple2.mk hi lo))
    else
      (pure (Rust_primitives.Hax.Tuple2.mk hi lo));
  (pure (Rust_primitives.Hax.Tuple2.mk lo hi))

--  Standard field multiplication: H * X mod p(x).
--  Bit-by-bit schoolbook with online reduction.
def gf128_mul (h : (RustArray u8 16)) (x : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let h0 : u64 ← (le_u64 (← (Rust_primitives.unsize h)) (0 : usize));
  let h1 : u64 ← (le_u64 (← (Rust_primitives.unsize h)) (8 : usize));
  let x0 : u64 ← (le_u64 (← (Rust_primitives.unsize x)) (0 : usize));
  let x1 : u64 ← (le_u64 (← (Rust_primitives.unsize x)) (8 : usize));
  let v_lo : u64 := x0;
  let v_hi : u64 := x1;
  let r_lo : u64 := (0 : u64);
  let r_hi : u64 := (0 : u64);
  let ⟨r_hi, r_lo, v_hi, v_lo⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : i32)
      (64 : i32)
      (fun ⟨r_hi, r_lo, v_hi, v_lo⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple4.mk r_hi r_lo v_hi v_lo)
      (fun ⟨r_hi, r_lo, v_hi, v_lo⟩ i =>
        (do
        let ⟨r_hi, r_lo⟩ ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← (h0 >>>? i)) &&&? (1 : u64)))
            (1 : u64))) then
            let r_lo : u64 ← (r_lo ^^^? v_lo);
            let r_hi : u64 ← (r_hi ^^^? v_hi);
            (pure (Rust_primitives.Hax.Tuple2.mk r_hi r_lo))
          else
            (pure (Rust_primitives.Hax.Tuple2.mk r_hi r_lo));
        let ⟨tmp0, tmp1⟩ ← (gf128_mul_x v_lo v_hi);
        let v_lo : u64 := tmp0;
        let v_hi : u64 := tmp1;
        let _ := Rust_primitives.Hax.Tuple0.mk;
        (pure (Rust_primitives.Hax.Tuple4.mk r_hi r_lo v_hi v_lo)) :
        RustM (Rust_primitives.Hax.Tuple4 u64 u64 u64 u64))));
  let ⟨r_hi, r_lo, v_hi, v_lo⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : i32)
      (64 : i32)
      (fun ⟨r_hi, r_lo, v_hi, v_lo⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple4.mk r_hi r_lo v_hi v_lo)
      (fun ⟨r_hi, r_lo, v_hi, v_lo⟩ i =>
        (do
        let ⟨r_hi, r_lo⟩ ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← (h1 >>>? i)) &&&? (1 : u64)))
            (1 : u64))) then
            let r_lo : u64 ← (r_lo ^^^? v_lo);
            let r_hi : u64 ← (r_hi ^^^? v_hi);
            (pure (Rust_primitives.Hax.Tuple2.mk r_hi r_lo))
          else
            (pure (Rust_primitives.Hax.Tuple2.mk r_hi r_lo));
        let ⟨tmp0, tmp1⟩ ← (gf128_mul_x v_lo v_hi);
        let v_lo : u64 := tmp0;
        let v_hi : u64 := tmp1;
        let _ := Rust_primitives.Hax.Tuple0.mk;
        (pure (Rust_primitives.Hax.Tuple4.mk r_hi r_lo v_hi v_lo)) :
        RustM (Rust_primitives.Hax.Tuple4 u64 u64 u64 u64))));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let result : (RustArray u8 16) ← (put_le_u64 result (0 : usize) r_lo);
  let result : (RustArray u8 16) ← (put_le_u64 result (8 : usize) r_hi);
  (pure result)

--  x^{-128} mod p(x) = x^127 + x^124 + x^121 + x^114 + 1 (RFC 8452, Section 3).
--  As a Block in LE bit order:
--    bit 0 -> byte 0 bit 0
--    bit 114 -> byte 14 bit 2
--    bit 121 -> byte 15 bit 1
--    bit 124 -> byte 15 bit 4
--    bit 127 -> byte 15 bit 7
def XINV128 : (RustArray u8 16) :=
  RustM.of_isOk
    (do
    #v[(1 : u8),
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
         (4 : u8),
         (146 : u8)])
    (by rfl)

--  POLYVAL dot product: dot(H, X) = H * X * x^{-128} mod p(x).
-- 
--  Computed as gf128_mul(gf128_mul(H, X), XINV128).
def polyval_mul (h : (RustArray u8 16)) (x : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let hx : (RustArray u8 16) ← (gf128_mul h x);
  (gf128_mul hx XINV128)

--  POLYVAL(H, X_1, ..., X_n):
--    S_0 = 0; S_j = dot(S_{j-1} XOR X_j, H); result = S_n
def polyval
    (h : (RustArray u8 16))
    (blocks : (RustArray (RustArray u8 16) 32))
    (num_blocks : usize) :
    RustM (RustArray u8 16) := do
  let s : (RustArray u8 16) := ZERO_BLOCK;
  (Rust_primitives.Hax.Folds.fold_range_cf
    (0 : usize)
    MAX_BLOCKS
    (fun s _ => (do (pure true) : RustM Bool))
    s
    (fun s i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
        (pure (Core_models.Ops.Control_flow.ControlFlow.Break
          (Rust_primitives.Hax.Tuple2.mk Rust_primitives.Hax.Tuple0.mk s)))
      else
        let s : (RustArray u8 16) ← (xor_block s (← blocks[i]_?));
        (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
          (← (polyval_mul h s)))) :
      RustM
      (Core_models.Ops.Control_flow.ControlFlow
        (Rust_primitives.Hax.Tuple2
          Rust_primitives.Hax.Tuple0
          (RustArray u8 16))
        (RustArray u8 16)))))

--  Helper for `derive_keys`: encrypts a per-ctr nonce-derived block.
--  Factored out so the inner mutation pattern doesn't span both
--  `auth_key` and `enc_key`. haxpipeT's `localMutation` lifts
--  match-arm-internal assignments to let-rebindings but cannot
--  thread two different outer variables through a single fold
--  accumulator. The original loop iterated 0..4 mutating `auth_key`
--  on ctr 0..1 and `enc_key` on ctr 2..3 inside one match. Splitting
--  the loop along the auth/enc axis keeps each fold's accumulator
--  single-variable, which the verified pipeline lifts cleanly.
def derive_keys_block
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (ctr : u32) :
    RustM (RustArray u8 16) := do
  let input : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      input
      (0 : usize)
      (← (Rust_primitives.Hax.cast_op (← (ctr &&&? (255 : u32))))));
  let input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      input
      (1 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (ctr >>>? (8 : i32))) &&&? (255 : u32))))));
  let input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      input
      (2 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (ctr >>>? (16 : i32))) &&&? (255 : u32))))));
  let input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      input
      (3 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (ctr >>>? (24 : i32))) &&&? (255 : u32))))));
  let input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (12 : usize)
      (fun input _ => (do (pure true) : RustM Bool))
      input
      (fun input j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          input
          (← ((4 : usize) +? j))
          (← nonce[j]_?)) :
        RustM (RustArray u8 16))));
  (aes128_encrypt key input)

def derive_keys (key : (RustArray u8 16)) (nonce : (RustArray u8 12)) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) (RustArray u8 16)) := do
  let auth_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let enc_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let enc0 : (RustArray u8 16) ← (derive_keys_block key nonce (0 : u32));
  let auth_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun auth_key _ => (do (pure true) : RustM Bool))
      auth_key
      (fun auth_key j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          auth_key
          j
          (← enc0[j]_?)) :
        RustM (RustArray u8 16))));
  let enc1 : (RustArray u8 16) ← (derive_keys_block key nonce (1 : u32));
  let auth_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun auth_key _ => (do (pure true) : RustM Bool))
      auth_key
      (fun auth_key j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          auth_key
          (← ((8 : usize) +? j))
          (← enc1[j]_?)) :
        RustM (RustArray u8 16))));
  let enc2 : (RustArray u8 16) ← (derive_keys_block key nonce (2 : u32));
  let enc_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun enc_key _ => (do (pure true) : RustM Bool))
      enc_key
      (fun enc_key j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          enc_key
          j
          (← enc2[j]_?)) :
        RustM (RustArray u8 16))));
  let enc3 : (RustArray u8 16) ← (derive_keys_block key nonce (3 : u32));
  let enc_key : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun enc_key _ => (do (pure true) : RustM Bool))
      enc_key
      (fun enc_key j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          enc_key
          (← ((8 : usize) +? j))
          (← enc3[j]_?)) :
        RustM (RustArray u8 16))));
  (pure (Rust_primitives.Hax.Tuple2.mk auth_key enc_key))

def gcm_siv_ctr_increment (ctr : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let val : u32 ←
    (Rust_primitives.Hax.Machine_int.bitor
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← (Rust_primitives.Hax.Machine_int.bitor
          (← (Rust_primitives.Hax.cast_op (← ctr[(0 : usize)]_?)))
          (← ((← (Rust_primitives.Hax.cast_op (← ctr[(1 : usize)]_?)))
            <<<? (8 : i32)))))
        (← ((← (Rust_primitives.Hax.cast_op (← ctr[(2 : usize)]_?)))
          <<<? (16 : i32)))))
      (← ((← (Rust_primitives.Hax.cast_op (← ctr[(3 : usize)]_?)))
        <<<? (24 : i32))));
  let val : u32 ← (Core_models.Num.Impl_8.wrapping_add val (1 : u32));
  let ctr : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      ctr
      (0 : usize)
      (← (Rust_primitives.Hax.cast_op (← (val &&&? (255 : u32))))));
  let ctr : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      ctr
      (1 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (val >>>? (8 : i32))) &&&? (255 : u32))))));
  let ctr : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      ctr
      (2 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (val >>>? (16 : i32))) &&&? (255 : u32))))));
  let ctr : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      ctr
      (3 : usize)
      (← (Rust_primitives.Hax.cast_op
        (← ((← (val >>>? (24 : i32))) &&&? (255 : u32))))));
  (pure ctr)

def gcm_siv_ctr_crypt
    (enc_key : (RustArray u8 16))
    (tag : (RustArray u8 16))
    (in_blocks : (RustArray (RustArray u8 16) 32))
    (out_blocks : (RustArray (RustArray u8 16) 32))
    (num_blocks : usize)
    (msg_len : usize) :
    RustM (RustArray (RustArray u8 16) 32) := do
  let ctr : (RustArray u8 16) := tag;
  let ctr : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      ctr
      (15 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← ctr[(15 : usize)]_?)
        (128 : u8))));
  let ⟨ctr, out_blocks⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun ⟨ctr, out_blocks⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk ctr out_blocks)
      (fun ⟨ctr, out_blocks⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk ctr out_blocks))))
        else
          let keystream : (RustArray u8 16) ← (aes128_encrypt enc_key ctr);
          let ctr : (RustArray u8 16) ← (gcm_siv_ctr_increment ctr);
          let block_start : usize ← (i *? (16 : usize));
          let remaining : usize ←
            if (← (Rust_primitives.Hax.Machine_int.gt msg_len block_start)) then
              (msg_len -? block_start)
            else
              (pure (0 : usize));
          let bytes_in_block : usize ←
            if
            (← (Rust_primitives.Hax.Machine_int.gt remaining (16 : usize))) then
              (pure (16 : usize))
            else
              (pure remaining);
          let out_blocks : (RustArray (RustArray u8 16) 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out_blocks
              i
              (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize))));
          let out_blocks : (RustArray (RustArray u8 16) 32) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (16 : usize)
              (fun out_blocks _ => (do (pure true) : RustM Bool))
              out_blocks
              (fun out_blocks j =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt j bytes_in_block)) then
                  let out_blocks : (RustArray (RustArray u8 16) 32) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      out_blocks
                      i
                      (←
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                        (← out_blocks[i]_?)
                        j
                        (← ((← (← in_blocks[i]_?)[j]_?)
                          ^^^? (← keystream[j]_?))))));
                  (pure out_blocks)
                else
                  (pure out_blocks) :
                RustM (RustArray (RustArray u8 16) 32))));
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk ctr out_blocks))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2
              (RustArray u8 16)
              (RustArray (RustArray u8 16) 32)))
          (Rust_primitives.Hax.Tuple2
            (RustArray u8 16)
            (RustArray (RustArray u8 16) 32))))));
  (pure out_blocks)

def build_polyval_input
    (aad : (RustArray (RustArray u8 16) 32))
    (num_aad_blocks : usize)
    (msg : (RustArray (RustArray u8 16) 32))
    (num_msg_blocks : usize)
    (aad_len : usize)
    (msg_len : usize)
    (out : (RustArray (RustArray u8 16) 32)) :
    RustM
    (Rust_primitives.Hax.Tuple2 (RustArray (RustArray u8 16) 32) usize)
    := do
  let idx : usize := (0 : usize);
  let ⟨idx, out⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun ⟨idx, out⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk idx out)
      (fun ⟨idx, out⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_aad_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk idx out))))
        else
          let out : (RustArray (RustArray u8 16) 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              idx
              (← aad[i]_?));
          let idx : usize ← (idx +? (1 : usize));
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk idx out))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2 usize (RustArray (RustArray u8 16) 32)))
          (Rust_primitives.Hax.Tuple2
            usize
            (RustArray (RustArray u8 16) 32))))));
  let ⟨idx, out⟩ ←
    (Rust_primitives.Hax.Folds.fold_range_cf
      (0 : usize)
      MAX_BLOCKS
      (fun ⟨idx, out⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk idx out)
      (fun ⟨idx, out⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.ge i num_msg_blocks)) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Rust_primitives.Hax.Tuple2.mk
              Rust_primitives.Hax.Tuple0.mk
              (Rust_primitives.Hax.Tuple2.mk idx out))))
        else
          let out : (RustArray (RustArray u8 16) 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              idx
              (← msg[i]_?));
          let idx : usize ← (idx +? (1 : usize));
          (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
            (Rust_primitives.Hax.Tuple2.mk idx out))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Rust_primitives.Hax.Tuple2
            Rust_primitives.Hax.Tuple0
            (Rust_primitives.Hax.Tuple2 usize (RustArray (RustArray u8 16) 32)))
          (Rust_primitives.Hax.Tuple2
            usize
            (RustArray (RustArray u8 16) 32))))));
  let aad_bits : u64 ←
    (Core_models.Num.Impl_9.wrapping_mul
      (← (Rust_primitives.Hax.cast_op aad_len))
      (8 : u64));
  let msg_bits : u64 ←
    (Core_models.Num.Impl_9.wrapping_mul
      (← (Rust_primitives.Hax.cast_op msg_len))
      (8 : u64));
  let len_block : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let len_block : (RustArray u8 16) ←
    (put_le_u64 len_block (0 : usize) aad_bits);
  let len_block : (RustArray u8 16) ←
    (put_le_u64 len_block (8 : usize) msg_bits);
  let out : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      idx
      len_block);
  let idx : usize ← (idx +? (1 : usize));
  let hax_temp_output : usize := idx;
  (pure (Rust_primitives.Hax.Tuple2.mk out hax_temp_output))

def bytes_to_blocks
    (data : (RustSlice u8))
    (data_len : usize)
    (blocks : (RustArray (RustArray u8 16) 32)) :
    RustM
    (Rust_primitives.Hax.Tuple2 (RustArray (RustArray u8 16) 32) usize)
    := do
  if (← (Rust_primitives.Hax.Machine_int.eq data_len (0 : usize))) then
    (pure (Rust_primitives.Hax.Tuple2.mk blocks (0 : usize)))
  else
    let num_blocks : usize ← ((← (data_len +? (15 : usize))) /? (16 : usize));
    let blocks : (RustArray (RustArray u8 16) 32) ←
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
            let blocks : (RustArray (RustArray u8 16) 32) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                blocks
                i
                (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize))));
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (← (Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                (16 : usize)
                (fun blocks _ => (do (pure true) : RustM Bool))
                blocks
                (fun blocks j =>
                  (do
                  let idx : usize ← ((← (i *? (16 : usize))) +? j);
                  if (← (Rust_primitives.Hax.Machine_int.lt idx data_len)) then
                    let blocks : (RustArray (RustArray u8 16) 32) ←
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                        blocks
                        i
                        (←
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                          (← blocks[i]_?)
                          j
                          (← data[idx]_?))));
                    (pure blocks)
                  else
                    (pure blocks) :
                  RustM (RustArray (RustArray u8 16) 32))))))) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Rust_primitives.Hax.Tuple2
              Rust_primitives.Hax.Tuple0
              (RustArray (RustArray u8 16) 32))
            (RustArray (RustArray u8 16) 32)))));
    let hax_temp_output : usize := num_blocks;
    (pure (Rust_primitives.Hax.Tuple2.mk blocks hax_temp_output))

def blocks_to_bytes
    (blocks : (RustArray (RustArray u8 16) 32))
    (byte_len : usize)
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      byte_len
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let block_idx : usize ← (i /? (16 : usize));
        let byte_idx : usize ← (i %? (16 : usize));
        if
        (← ((← (Rust_primitives.Hax.Machine_int.lt block_idx MAX_BLOCKS))
          &&? (← (Rust_primitives.Hax.Machine_int.lt
            i
            (← (Core_models.Slice.Impl.len u8 out)))))) then
          let out : (RustSlice u8) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              i
              (← (← blocks[block_idx]_?)[byte_idx]_?));
          (pure out)
        else
          (pure out) :
        RustM (RustSlice u8))));
  (pure out)

def aes_gcm_siv_seal
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (aad_len : usize)
    (plaintext : (RustSlice u8))
    (pt_len : usize) :
    RustM
    (Rust_primitives.Hax.Tuple3
      (RustArray (RustArray u8 16) 32)
      usize
      (RustArray u8 16))
    := do
  let ⟨auth_key, enc_key⟩ ← (derive_keys key nonce);
  let aad_blocks : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ⟨tmp0, out⟩ ← (bytes_to_blocks aad aad_len aad_blocks);
  let aad_blocks : (RustArray (RustArray u8 16) 32) := tmp0;
  let num_aad_blocks : usize := out;
  let pt_blocks : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ⟨tmp0, out⟩ ← (bytes_to_blocks plaintext pt_len pt_blocks);
  let pt_blocks : (RustArray (RustArray u8 16) 32) := tmp0;
  let num_pt_blocks : usize := out;
  let pv_input : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ⟨tmp0, out⟩ ←
    (build_polyval_input
      aad_blocks
      num_aad_blocks
      pt_blocks
      num_pt_blocks
      aad_len
      pt_len
      pv_input);
  let pv_input : (RustArray (RustArray u8 16) 32) := tmp0;
  let pv_count : usize := out;
  let pv_result : (RustArray u8 16) ← (polyval auth_key pv_input pv_count);
  let tag_input : (RustArray u8 16) := pv_result;
  let tag_input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (12 : usize)
      (fun tag_input _ => (do (pure true) : RustM Bool))
      tag_input
      (fun tag_input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          tag_input
          i
          (← ((← tag_input[i]_?) ^^^? (← nonce[i]_?)))) :
        RustM (RustArray u8 16))));
  let tag_input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      tag_input
      (15 : usize)
      (← ((← tag_input[(15 : usize)]_?) &&&? (127 : u8))));
  let tag : (RustArray u8 16) ← (aes128_encrypt enc_key tag_input);
  let ct_blocks : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ct_blocks : (RustArray (RustArray u8 16) 32) ←
    if (← (Rust_primitives.Hax.Machine_int.gt pt_len (0 : usize))) then
      let ct_blocks : (RustArray (RustArray u8 16) 32) ←
        (gcm_siv_ctr_crypt
          enc_key
          tag
          pt_blocks
          ct_blocks
          num_pt_blocks
          pt_len);
      (pure ct_blocks)
    else
      (pure ct_blocks);
  (pure (Rust_primitives.Hax.Tuple3.mk ct_blocks num_pt_blocks tag))

def aes_gcm_siv_open
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (aad_len : usize)
    (ciphertext : (RustSlice u8))
    (ct_len : usize)
    (tag : (RustArray u8 16)) :
    RustM
    (Core_models.Option.Option
      (Rust_primitives.Hax.Tuple2 (RustArray (RustArray u8 16) 32) usize))
    := do
  let ⟨auth_key, enc_key⟩ ← (derive_keys key nonce);
  let ct_blocks : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ⟨tmp0, out⟩ ← (bytes_to_blocks ciphertext ct_len ct_blocks);
  let ct_blocks : (RustArray (RustArray u8 16) 32) := tmp0;
  let num_ct_blocks : usize := out;
  let pt_blocks : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let pt_blocks : (RustArray (RustArray u8 16) 32) ←
    if (← (Rust_primitives.Hax.Machine_int.gt ct_len (0 : usize))) then
      let pt_blocks : (RustArray (RustArray u8 16) 32) ←
        (gcm_siv_ctr_crypt
          enc_key
          tag
          ct_blocks
          pt_blocks
          num_ct_blocks
          ct_len);
      (pure pt_blocks)
    else
      (pure pt_blocks);
  let aad_blocks : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ⟨tmp0, out⟩ ← (bytes_to_blocks aad aad_len aad_blocks);
  let aad_blocks : (RustArray (RustArray u8 16) 32) := tmp0;
  let num_aad_blocks : usize := out;
  let pv_input : (RustArray (RustArray u8 16) 32) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (32 : usize));
  let ⟨tmp0, out⟩ ←
    (build_polyval_input
      aad_blocks
      num_aad_blocks
      pt_blocks
      num_ct_blocks
      aad_len
      ct_len
      pv_input);
  let pv_input : (RustArray (RustArray u8 16) 32) := tmp0;
  let pv_count : usize := out;
  let pv_result : (RustArray u8 16) ← (polyval auth_key pv_input pv_count);
  let tag_input : (RustArray u8 16) := pv_result;
  let tag_input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (12 : usize)
      (fun tag_input _ => (do (pure true) : RustM Bool))
      tag_input
      (fun tag_input i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          tag_input
          i
          (← ((← tag_input[i]_?) ^^^? (← nonce[i]_?)))) :
        RustM (RustArray u8 16))));
  let tag_input : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      tag_input
      (15 : usize)
      (← ((← tag_input[(15 : usize)]_?) &&&? (127 : u8))));
  let expected_tag : (RustArray u8 16) ← (aes128_encrypt enc_key tag_input);
  let diff : u8 := (0 : u8);
  let diff : u8 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun diff _ => (do (pure true) : RustM Bool))
      diff
      (fun diff i =>
        (do
        (Rust_primitives.Hax.Machine_int.bitor
          diff
          (← ((← expected_tag[i]_?) ^^^? (← tag[i]_?)))) :
        RustM u8)));
  if (← (Rust_primitives.Hax.Machine_int.ne diff (0 : u8))) then
    (pure Core_models.Option.Option.None)
  else
    (pure (Core_models.Option.Option.Some
      (Rust_primitives.Hax.Tuple2.mk pt_blocks num_ct_blocks)))

end Aesgcmsiv_hax

