import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.JensenFormula

namespace Commons.Analysis.Complex

/-- **Jensen's formula, inequality form**: if the circle average of `log ‖f‖` on the circle of
radius `R` around `c` is at most `B`, then the divisor-weighted sum
`∑ᶠ u, divisor f (closedBall c R) u * log (R / ‖c - u‖)` (the "counting function" of the zeros of
`f`) is at most `B - log ‖f c‖`.

This is the direct consequence of Mathlib's Jensen formula
`AnalyticOnNhd.circleAverage_log_norm`,
`circleAverage (log ‖f ·‖) c R = ∑ᶠ u, divisor f (closedBall c R) u * log (R * ‖c - u‖⁻¹) + log ‖f c‖`,
combined with the hypothesis `havg`. -/
theorem finsum_divisor_mul_log_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hfc : f c ≠ 0)
    (havg : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) c R ≤ B) :
    (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ) *
      Real.log (R / ‖c - u‖)) ≤ B - Real.log ‖f c‖ := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := by rwa [abs_of_pos hR]
  -- Jensen's formula
  have hJ := hf'.circleAverage_log_norm hRne hfc
  rw [abs_of_pos hR] at hJ
  -- Identify the target sum with `circleAverage - log ‖f c‖`
  have key : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) c R - Real.log ‖f c‖
      = ∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ) *
          Real.log (R / ‖c - u‖) := by
    rw [hJ, add_sub_cancel_right]
    refine finsum_congr fun u => ?_
    rw [div_eq_mul_inv]
  rw [← key]
  linarith

end Commons.Analysis.Complex