import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol

namespace Work.HilbertSymbol

/-!
# The Hilbert symbol `(-1, -1)_2 = -1`

At the place `2`, both arguments are the unit `-1 ∈ ℚˣ`, whose `2`-adic valuation is `0` and whose
`2`-adic unit part is `-1 ∈ ℤ_[2]ˣ`.  The explicit formula for `(·,·)_2` therefore reduces to
`signOf (ε(-1)ε(-1) + 0 + 0)`, and `ε(-1) = 1` (since `-1 ≡ 3 = 1 + 2·1 (mod 4)`), so the
exponent is `1` and `(-1,-1)_2 = signOf 1 = -1`.
-/

/-- The `2`-adic unit part of `-1` is `-1`. -/
private theorem unitPart_two_neg_one : unitPart 2 (-1 : ℚˣ) = -1 := by
  apply Units.ext
  apply PadicInt.ext
  rw [unitPart_coe, unitVal, padicVal_neg, padicVal_one, neg_zero, zpow_zero, one_mul]
  norm_num

/-- `epsZ (-1) = 1`, i.e. `-1 ≡ 3 (mod 4)`. -/
private theorem epsZ_neg_one : epsZ (-1 : ℤ_[2]ˣ) = 1 := by simp [epsZ]

/-- `omegaZ (-1) = 0`, i.e. `-1 ≡ 7 (mod 8)`. -/
private theorem omegaZ_neg_one : omegaZ (-1 : ℤ_[2]ˣ) = 0 := by simp [omegaZ]

theorem hilbertSymbolTwo_neg_one_neg_one :
    hilbertSymbolTwo (-1 : ℚˣ) (-1 : ℚˣ) = -1 := by
  rw [hilbertSymbolTwo, unitPart_two_neg_one, padicVal_neg, padicVal_one, epsZ_neg_one,
    omegaZ_neg_one]
  norm_num [signOf]

end Work.HilbertSymbol
