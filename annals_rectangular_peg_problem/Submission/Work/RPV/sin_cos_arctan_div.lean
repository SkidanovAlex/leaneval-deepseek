import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPV

theorem sin_cos_arctan_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sin (Real.arctan (a / b)) = a / Real.sqrt (a ^ 2 + b ^ 2) ∧
    Real.cos (Real.arctan (a / b)) = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hs : Real.sqrt (1 + (a / b) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / b := by
    have h : 1 + (a / b) ^ 2 = (a ^ 2 + b ^ 2) / b ^ 2 := by
      field_simp
      ring
    rw [h, Real.sqrt_div' (a ^ 2 + b ^ 2) (y := b ^ 2) (by positivity),
      Real.sqrt_sq (le_of_lt hb)]
  constructor
  · rw [Real.sin_arctan, hs, div_div_div_cancel_right₀ hb0]
  · rw [Real.cos_arctan, hs, one_div, inv_div]

end Work.RPV
