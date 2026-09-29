import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.chunks_eq_chunkDigits
import Submission.Work.IntLib.stripFalses_map_bit
import Submission.Work.IntLib.encodeNatBridge

/-!
# The `chunk` word's push order is the encoding of the digit list

The `chunk` word reads the canonical bit stream `x.bits` (least significant bit first), padded with
zeros to `b * N` positions, and for each `j < N` pushes the glyph block
`blk ps b j = [cons, pos] ++ <bits of the j-th digit> ++ [iend]`, then a final `nil`.

This file proves that this push order is *exactly* `Val.enc (intList (chunkDigits x.bits b N))`,
i.e. the encoding of the `cons`-chain of the `N` base-`2^b` digits of `x` — the specification the
program-level correctness proof of the `chunk` word needs.

The identity is purely combinatorial (the hypotheses `1 ≤ b` and `x < 2^(b*N)` only serve the
caller's bookkeeping): the `j`-th push block reads the window of positions `b*j … b*j+b-1` of the
zero-padded stream, which is the `j`-th base-`2^b` digit of `x`, canonically encoded.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## `ofBits` of a zero-padded, windowed bit list -/

theorem ofBits_replicate_false (m : ℕ) : ofBits (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ofBits_cons]; simp [ih]

theorem ofBits_append_replicate_false (xs : List Bool) (m : ℕ) :
    ofBits (xs ++ List.replicate m false) = ofBits xs := by
  rw [ofBits_append, ofBits_replicate_false, Nat.mul_zero, Nat.add_zero]

/-- `ofBits` of the high part of a bit list is the value divided by `2^k`. -/
theorem ofBits_drop_div (xs : List Bool) (k : ℕ) : ofBits (xs.drop k) = ofBits xs / 2 ^ k := by
  have hsplit := ofBits_take_drop xs k
  have hlt : ofBits (xs.take k) < 2 ^ k := by
    have h := ofBits_lt_two_pow (xs.take k)
    rw [List.length_take] at h
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (Nat.min_le_left _ _))
  rw [hsplit, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) k), Nat.div_eq_of_lt hlt,
    zero_add]

/-- The value read from the bit positions `k … k+b-1` of a bit list. -/
theorem ofBits_drop_take (xs : List Bool) (k b : ℕ) :
    ofBits ((xs.drop k).take b) = ofBits xs / 2 ^ k % 2 ^ b := by
  rw [ofBits_take_mod, ofBits_drop_div]

/-- Reading a `b`-bit window of the zero-padded bit list `x.bits ++ 0…0` gives the same value as
reading it from `x.bits` itself: the padding only contributes zeros. -/
theorem ofBits_window (x b N j : ℕ) :
    ofBits (((x.bits ++ List.replicate (b * N - x.size) false).drop (b * j)).take b)
      = ofBits ((x.bits.drop (b * j)).take b) := by
  rw [ofBits_drop_take, ofBits_drop_take, ofBits_append_replicate_false, ofBits_bits]

/-! ## The per-block identity -/

/-- The encoding of `Val.int d` for a natural number `d`. -/
theorem enc_int_ofNat (d : ℕ) :
    (Val.int (d : ℤ)).enc = Glyph.pos :: (d.bits.map Glyph.bit ++ [Glyph.iend]) := by
  rw [enc_int, if_neg (by simp), Int.natAbs_natCast, encodeNat_eq_bits]

/-- The glyph block pushed for one digit is `cons` followed by the encoding of that digit. -/
theorem blk_eq_enc (x b N j : ℕ) :
    blk (x.bits ++ List.replicate (b * N - x.size) false) b j
      = Glyph.cons :: (Val.int ((ofBits ((x.bits.drop (b * j)).take b)) : ℤ)).enc := by
  have hS : stripFalses
        ((((x.bits ++ List.replicate (b * N - x.size) false).drop (b * j)).take b).map Glyph.bit)
      = ((ofBits ((x.bits.drop (b * j)).take b)).bits).map Glyph.bit := by
    rw [stripFalses_map_bit, ofBits_window]
  rw [blk, hS, enc_int_ofNat]
  rfl

/-! ## `flatMap` over a mapped list -/

/-- `flatMap` over a mapped list. -/
theorem flatMap_map {α β γ : Type*} (F : β → List γ) (g : α → β) (l : List α) :
    List.flatMap F (l.map g) = List.flatMap (fun a => F (g a)) l := by
  unfold List.flatMap
  rw [List.map_map]
  exact congrArg List.flatten (List.map_congr_left (fun a _ => rfl))

/-! ## `Val.enc` of an `intList` -/

/-- The encoding of a `cons`-chain of integer values. -/
theorem enc_ofList_flatMap (vs : List Val) :
    Val.enc (ofList vs) =
      List.flatMap (fun v => Glyph.cons :: Val.enc v) vs ++ [Glyph.nil] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change Glyph.cons :: (Val.enc v ++ Val.enc (ofList vs))
      = List.flatMap (fun v => Glyph.cons :: Val.enc v) (v :: vs) ++ [Glyph.nil]
    rw [List.flatMap_cons, ih, List.append_assoc]
    rfl

/-- `intList` is the `ofList` of the entries coerced to integer values. -/
theorem intList_eq_map (l : List ℕ) :
    intList l = ofList (l.map (fun d : ℕ => Val.int (d : ℤ))) := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    change Val.cons (Val.int (d : ℤ)) (intList ds) =
      Val.cons (Val.int (d : ℤ)) (ofList (ds.map (fun d : ℕ => Val.int (d : ℤ))))
    rw [ih]

/-- The encoding of the `cons`-chain of the entries of `l`, each block prefixed by `cons`. -/
theorem enc_intList_flatMap (l : List ℕ) :
    Val.enc (intList l) =
      List.flatMap (fun d : ℕ => Glyph.cons :: (Val.int (d : ℤ)).enc) l ++ [Glyph.nil] := by
  rw [intList_eq_map l, enc_ofList_flatMap]
  congr 1
  exact flatMap_map (fun v => Glyph.cons :: Val.enc v) (fun d : ℕ => Val.int (d : ℤ)) l

/-! ## The main statement -/

theorem range_blk_enc (x b N : ℕ) (hb : 1 ≤ b) (hx : x < 2 ^ (b * N)) :
    List.flatMap (Work.IntLib.blk (x.bits ++ List.replicate (b * N - x.size) false) b) (List.range N)
        ++ [HvdH.Glyph.nil] =
      HvdH.Val.enc (HvdH.intList (Work.IntLib.chunkDigits x.bits b N)) := by
  have hchunk : chunkDigits x.bits b N
      = (List.range N).map (fun j => ofBits ((x.bits.drop (b * j)).take b)) := rfl
  have hmain : List.flatMap (blk (x.bits ++ List.replicate (b * N - x.size) false) b) (List.range N)
      = List.flatMap
          (fun j => Glyph.cons :: (Val.int ((ofBits ((x.bits.drop (b * j)).take b)) : ℤ)).enc)
          (List.range N) := by
    apply List.flatMap_congr
    intro j _
    exact blk_eq_enc x b N j
  rw [hchunk, hmain, enc_intList_flatMap]
  congr 1
  exact (flatMap_map (fun d : ℕ => Glyph.cons :: (Val.int (d : ℤ)).enc)
    (fun j => ofBits ((x.bits.drop (b * j)).take b)) (List.range N)).symm

end Work.IntLib
