import Mathlib

/-!
# Jensen's mean value inequality for `log ‖f‖`

If `f` is analytic on the closed ball of centre `0` and radius `R > 0` and `f 0 ≠ 0`, then the
value of `log ‖f‖` at the centre is bounded by its circle average over the boundary, i.e.

`Real.log ‖f 0‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) 0 R`.

This is an immediate consequence of Jensen's formula (`AnalyticOnNhd.circleAverage_log_norm`):
the circle average equals `log ‖f 0‖` plus the contribution
`∑ᶠ u, (divisor f (closedBall 0 R)) u * log (R * ‖u‖⁻¹)` of the zeros of `f` in the closed ball,
and every summand of that contribution is non-negative because the divisor of an analytic function
is non-negative and `log (R * ‖u‖⁻¹) ≥ 0` for `‖u‖ ≤ R`.
-/

namespace Work.Holonomy3

theorem jensen_mean_ineq (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) 0 R := by
  have habs : |R| = R := abs_of_pos hR
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall 0 |R|) := by
    rw [habs]; exact hf
  have hJ := hf'.circleAverage_log_norm (ne_of_gt hR) hf0
  rw [hJ]
  have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor f (Metric.closedBall 0 |R|)) u : ℝ)
      * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |R|
    · have hd : (0 : ℝ) ≤ ((MeromorphicOn.divisor f (Metric.closedBall 0 |R|)) u : ℝ) := by
        exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' u)
      refine mul_nonneg hd ?_
      by_cases hu0 : u = 0
      · subst hu0; simp
      · have hn : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
        have hle : ‖u‖ ≤ R := by
          have h1 := Metric.mem_closedBall.mp hu
          rw [dist_eq_norm, sub_zero, habs] at h1
          exact h1
        apply Real.log_nonneg
        rw [← div_eq_mul_inv]
        simpa [zero_sub] using (one_le_div hn).mpr hle
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith

end Work.Holonomy3
