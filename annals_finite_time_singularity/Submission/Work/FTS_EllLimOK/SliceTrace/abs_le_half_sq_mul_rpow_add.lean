import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.SliceTrace

/-- The arithmetic–geometric mean inequality in the form
`|h| ≤ (h² s^{-η} + s^η)/2` for `s > 0`: the two summands are nonnegative and their
product is `h²`, so `2|h| = 2√(A B) ≤ A + B`. -/
theorem abs_le_half_sq_mul_rpow_add {η s h : ℝ} (hs : 0 < s) :
    |h| ≤ (h ^ 2 * s ^ (-η) + s ^ η) / 2 := by
  set A := h ^ 2 * s ^ (-η) with hAdef
  set B := s ^ η with hBdef
  have hs0 : 0 ≤ s := le_of_lt hs
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; exact Real.rpow_nonneg hs0 _
  -- the two summands multiply to `h ^ 2`
  have hAB : A * B = h ^ 2 := by
    rw [hAdef, hBdef, mul_assoc, ← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero, mul_one]
  -- `(A + B) ^ 2 - 4 h ^ 2 = (A - B) ^ 2 ≥ 0`
  have h4 : 4 * h ^ 2 ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
  have h2 : (2 * |h|) ^ 2 ≤ (A + B) ^ 2 := by nlinarith [abs_nonneg h, sq_abs h]
  have : 2 * |h| ≤ A + B := by nlinarith [abs_nonneg h, hA0, hB0, h2]
  linarith

end Work.FTS_EllLimOK.SliceTrace
