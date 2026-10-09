import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-! ## Bimultiplicativity of the archimedean Hilbert symbol

The archimedean symbol is `(a,b)_∞ = -1` iff `a < 0` and `b < 0`. Writing
`negZ a ∈ ZMod 2` for the parity of the sign of `a` (`1` when `a < 0`, `0` otherwise) and
using the isomorphism `signOf : ZMod 2 ≅ ℤˣ` of `Basic`, we have
`(a,b)_∞ = signOf (negZ a * negZ b)`. The result then reduces to the additivity of `negZ`
under multiplication, which is the classical "sign of a product" statement. -/

/-- The parity of the sign of a nonzero rational number: `1` when it is negative, `0` otherwise,
viewed in `ZMod 2`. -/
private def negZ (a : ℚˣ) : ZMod 2 := if (a : ℚ) < 0 then 1 else 0

/-- The archimedean Hilbert symbol is `signOf` applied to the product of the sign parities. -/
private lemma hilbertSymbolReal_eq_signOf_negZ (a b : ℚˣ) :
    hilbertSymbolReal a b = signOf (negZ a * negZ b) := by
  rw [hilbertSymbolReal]
  by_cases ha : (a : ℚ) < 0 <;> by_cases hb : (b : ℚ) < 0 <;>
    simp [negZ, ha, hb]

/-- The sign parity is additive under multiplication of nonzero rational numbers. -/
private lemma negZ_mul (a b : ℚˣ) : negZ (a * b) = negZ a + negZ b := by
  have hane : (a : ℚ) ≠ 0 := Units.ne_zero a
  have hbne : (b : ℚ) ≠ 0 := Units.ne_zero b
  rw [negZ, negZ, negZ, Units.val_mul]
  by_cases ha : (a : ℚ) < 0 <;> by_cases hb : (b : ℚ) < 0
  · have hp : ¬ ((a : ℚ) * (b : ℚ) < 0) :=
      not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg ha hb))
    simp [ha, hb, hp]
    decide
  · have hbpos : 0 < (b : ℚ) := lt_of_le_of_ne (not_lt.mp hb) (Ne.symm hbne)
    have hp : (a : ℚ) * (b : ℚ) < 0 := mul_neg_of_neg_of_pos ha hbpos
    simp [ha, hb, hp]
  · have hapos : 0 < (a : ℚ) := lt_of_le_of_ne (not_lt.mp ha) (Ne.symm hane)
    have hp : (a : ℚ) * (b : ℚ) < 0 := mul_neg_of_pos_of_neg hapos hb
    simp [ha, hb, hp]
  · have hapos : 0 < (a : ℚ) := lt_of_le_of_ne (not_lt.mp ha) (Ne.symm hane)
    have hbpos : 0 < (b : ℚ) := lt_of_le_of_ne (not_lt.mp hb) (Ne.symm hbne)
    have hp : ¬ ((a : ℚ) * (b : ℚ) < 0) :=
      not_lt.mpr (le_of_lt (mul_pos hapos hbpos))
    simp [ha, hb, hp]

theorem hilbertSymbolReal_mul_left (a₁ a₂ b : ℚˣ) :
    hilbertSymbolReal (a₁ * a₂) b = hilbertSymbolReal a₁ b * hilbertSymbolReal a₂ b := by
  rw [hilbertSymbolReal_eq_signOf_negZ, hilbertSymbolReal_eq_signOf_negZ,
    hilbertSymbolReal_eq_signOf_negZ, negZ_mul]
  rw [← signOf_add, add_mul]

end Work.HilbertSymbol
