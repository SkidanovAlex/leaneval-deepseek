import Mathlib.Analysis.MeanInequalities

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- For `0 ≤ x ≤ 1` and `0 ≤ ε ≤ 1`, one has `x ^ (1 - ε) / (ε + x) ≤ 1`.

This is the elementary weighted AM–GM bound `x ^ (1 - ε) ≤ (1 - ε) * x + ε ≤ x + ε`
(the second step since `ε * x ≥ 0`), combined with `div_le_one` when the denominator
`ε + x` is positive; when `ε + x = 0` both `x` and `ε` vanish and the quotient is `0`. -/
theorem rpow_sup_ineq (x ε : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    x ^ (1 - ε) / (ε + x) ≤ 1 := by
  have ham := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - ε) (w₂ := ε)
    (p₁ := x) (p₂ := 1) (by linarith) hε0 hx0 (by norm_num) (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at ham
  have key : x ^ (1 - ε) ≤ x + ε := by
    nlinarith [ham, mul_nonneg hε0 hx0]
  have hxε : 0 ≤ x + ε := by linarith
  rcases lt_or_eq_of_le hxε with hlt | heq
  · rw [div_le_one (b := ε + x) (by linarith)]; linarith
  · have hx : x = 0 := by linarith
    have hε : ε = 0 := by linarith
    subst hx; subst hε; norm_num

end Work.Spaces
