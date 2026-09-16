import Submission.ZagierHoffmanProof.AExpansion

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Regression checks for Carlitz's expansion of `A_n`

Concrete instances of `A_thakur_formula` over `ZMod 2` and `ZMod 3`.  (The characteristic-`p`
reductions are done with `CharP.cast_eq_zero` and `decide` on `ZMod` numerals, since `norm_num`
does not normalise numerals in `ZMod`.)
-/

namespace ZagierHoffmanPositiveChar

section Reg

attribute [local instance 100] Classical.decEq

lemma card_zmod2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
lemma card_zmod3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- `A_1 = -1` (also available directly). -/
example : (A (ZMod 2) 1 : (ZMod 2)[X]) = -1 := A_one_eq_neg_one (ZMod 2)

/-- The easy range `A_n = (-1)^n` for `n ≤ 2` over `F_2`. -/
example (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≤ 2) :
    (A (ZMod 2) n : (ZMod 2)[X]) = (-1 : (ZMod 2)[X]) ^ n :=
  A_eq_neg_one_pow (ZMod 2) n hn (by rw [card_zmod2]; exact hn2)

/-- `A_3 = X^2 + X + 1` over `F_2` (from the explicit formula). -/
example : (A (ZMod 2) 3 : (ZMod 2)[X]) = X ^ 2 + X + 1 := by
  have h := A_thakur_formula' (ZMod 2) 3 (by norm_num)
  rw [card_zmod2] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, mul_one, one_mul, pow_zero]
  norm_num
  rw [carlitzOne, card_zmod2]
  have h2 : ((2 : ℕ) : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero (ZMod 2)[X] 2
  linear_combination (norm := ring_nf) (-(1 + X)) * h2

/-- `A_5 = 1 + [1] + [1]^2` over `F_2` (Carlitz's formula with a nontrivial correction term). -/
example : (A (ZMod 2) 5 : (ZMod 2)[X])
    = 1 + carlitzOne (ZMod 2) + (carlitzOne (ZMod 2)) ^ 2 := by
  have h := A_thakur_formula' (ZMod 2) 5 (by norm_num)
  rw [card_zmod2] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, mul_one, one_mul, pow_zero]
  norm_num
  have h3 : (3 : ZMod 2) = 1 := by decide
  rw [h3]
  simp only [map_one, mul_one]
  rw [carlitzOne, card_zmod2]
  have h2 : ((2 : ℕ) : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero (ZMod 2)[X] 2
  linear_combination (norm := ring_nf) (-((X ^ 2 - X) ^ 2 + 1)) * h2

/-- `A_4 = 1 - [1]^2` over `F_3`. -/
example : (A (ZMod 3) 4 : (ZMod 3)[X]) = 1 - (carlitzOne (ZMod 3)) ^ 2 := by
  have h := A_thakur_formula' (ZMod 3) 4 (by norm_num)
  rw [card_zmod3] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, mul_one, one_mul, pow_zero]
  norm_num
  ring

end Reg

end ZagierHoffmanPositiveChar
