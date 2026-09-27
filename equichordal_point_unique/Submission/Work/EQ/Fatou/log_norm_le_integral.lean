import Mathlib
import Submission.Work.EQ.FatouDefs

/-!
# The sub-mean-value inequality for `log ‖f‖` (Jensen)

For a holomorphic `f` on the unit disc with `f 0 ≠ 0` and `0 < ρ < 1`, the value `log ‖f 0‖` is
bounded by the average of `log ‖f‖` over the circle of radius `ρ`.  This is the mean value
inequality for the subharmonic function `log ‖f‖`; formally it is Jensen's formula
(`AnalyticOnNhd.circleAverage_log_norm`) together with the nonnegativity of the divisor
correction term (the latter is `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`, together with
`log (ρ / ‖u‖) ≥ 0` for `u` in the closed ball of radius `ρ`).
-/

namespace Work.EQ.Fatou

theorem log_norm_le_integral (f : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (h0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ (2 * Real.pi)⁻¹ *
      ∫ θ in (0:ℝ)..2 * Real.pi, Real.log ‖f (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖ := by
  -- `f` is analytic on the closed ball of radius `ρ < 1`.
  have h_an : AnalyticOnNhd ℂ f (Metric.closedBall 0 |ρ|) := by
    rw [abs_of_pos hρ]
    intro x hx
    have hx1 : x ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      simpa using lt_of_le_of_lt hx hρ1
    exact hf.analyticAt (Metric.isOpen_ball.mem_nhds hx1)
  -- Jensen's formula at center `0` and radius `ρ`.
  have hJ := AnalyticOnNhd.circleAverage_log_norm (f := f) (c := 0) (R := ρ) (ne_of_gt hρ) h_an h0
  -- The divisor correction term is nonnegative: every summand is a product of a nonnegative
  -- integer (the vanishing order) and `log (ρ * ‖u‖⁻¹) ≥ 0` for `‖u‖ ≤ ρ`.
  have hsum_nonneg : 0 ≤ ∑ᶠ (u : ℂ),
      ((MeromorphicOn.divisor f (Metric.closedBall 0 |ρ|)) u : ℝ) * Real.log (ρ * ‖(0:ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall (0:ℂ) |ρ|
    · have hd : (0:ℝ) ≤ ((MeromorphicOn.divisor f (Metric.closedBall 0 |ρ|)) u : ℝ) :=
        Int.cast_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg h_an u)
      have hlog : 0 ≤ Real.log (ρ * ‖(0:ℂ) - u‖⁻¹) := by
        rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hρ] at hu
        have hnorm : ‖u‖ ≤ ρ := by simpa using hu
        have hnu : ‖(0:ℂ) - u‖ = ‖u‖ := by simp
        rcases eq_or_lt_of_le (norm_nonneg (u : ℂ)) with h0u | hpos
        · have hu0 : ‖u‖ = 0 := h0u.symm
          rw [hnu, hu0]; simp
        · apply Real.log_nonneg
          rw [hnu, ← div_eq_mul_inv, one_le_div hpos]
          exact hnorm
      exact mul_nonneg hd hlog
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  have hmain : Real.log ‖f 0‖ ≤ Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 ρ := by
    rw [hJ]
    exact le_add_of_nonneg_left hsum_nonneg
  -- Unfold the circle average into the interval integral appearing in the statement.
  have hca : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 ρ
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi,
          Real.log ‖f (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖ := by
    rw [Real.circleAverage_def]
    simp only [smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [circleMap, zero_add]
  exact hmain.trans (le_of_eq hca)

end Work.EQ.Fatou
