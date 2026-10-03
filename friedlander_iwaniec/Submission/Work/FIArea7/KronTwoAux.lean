/-
# `Submission.Work.FIArea7.KronTwoAux` — the character `χ₂ = χ₈ = (2|·)` revisited

`Work.FIArea7.kronTwo` (defined in `KronTwo.lean` by a three-way case split) is exactly Mathlib's
quadratic character `ZMod.χ₈`, so it is a `MulChar` and inherits multiplicativity from `χ₈`.  This
file records that bridge and its immediate consequences, so that the correction factor
`kronTwo a ^ ν` of `jacobiSym_reflection_mod4` can be manipulated as a character.
-/
import Mathlib
import Submission.Work.FIArea7.KronTwo

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open NumberTheorySymbols

/-- `kronTwo` is Mathlib's quadratic character `χ₈` on `ℤ/8ℤ`. -/
lemma kronTwo_eq_chi8 (a : ℤ) : kronTwo a = ZMod.χ₈ a := by
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  unfold kronTwo
  by_cases h : Even a
  · rw [if_pos h, Int.even_iff.mp h]; norm_num
  · rw [if_neg h, if_neg (fun hh => h (Int.even_iff.mpr hh))]

/-- `kronTwo` is multiplicative. -/
lemma kronTwo_mul (a b : ℤ) : kronTwo (a * b) = kronTwo a * kronTwo b := by
  simp only [kronTwo_eq_chi8]
  have : ((a * b : ℤ) : ZMod 8) = (a : ZMod 8) * (b : ZMod 8) := by push_cast; ring
  rw [this, map_mul]

/-- `kronTwo` depends only on the residue class modulo `8`. -/
lemma kronTwo_eq_of_modEq {a b : ℤ} (h : a ≡ b [ZMOD 8]) : kronTwo a = kronTwo b := by
  simp only [kronTwo_eq_chi8]
  have : (a : ZMod 8) = (b : ZMod 8) := by
    rw [ZMod.intCast_eq_intCast_iff]; exact h
  rw [this]

/-- `kronTwo a = ±1` for odd `a`. -/
lemma kronTwo_sq_of_odd {a : ℤ} (ha : Odd a) : kronTwo a ^ 2 = 1 := by
  rcases kronTwo_eq_one_or_neg_one_of_odd ha with h | h <;> rw [h] <;> norm_num

/-- `kronTwo` of an odd number is `±1`, so it equals its own inverse. -/
lemma kronTwo_mul_self_of_odd {a : ℤ} (ha : Odd a) : kronTwo a * kronTwo a = 1 := by
  rw [← sq]; exact kronTwo_sq_of_odd ha

/-- `kronTwo a = 1` for `a ≡ 1 (mod 8)`. -/
lemma kronTwo_eq_one_of_modEq_one {a : ℤ} (h : a ≡ 1 [ZMOD 8]) : kronTwo a = 1 := by
  rw [kronTwo_eq_of_modEq h]; norm_num [kronTwo]

end Work.FIArea7
