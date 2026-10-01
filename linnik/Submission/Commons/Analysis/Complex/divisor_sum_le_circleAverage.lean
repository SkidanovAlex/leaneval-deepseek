import Mathlib
import Submission.Commons.Analysis.Complex.finsum_divisor_mul_log_le

namespace Commons.Analysis.Complex

open Metric

/-- **Jensen / divisor-counting bound.**  If `f` is analytic on the closed ball of radius `R`
around `c`, `f c ≠ 0`, and the circle average of `log ‖f‖` on the circle of radius `R` is at
most `B`, then the number of zeros of `f` in the closed ball of radius `r < R`
(counted with multiplicity, i.e. the value of the divisor) is at most
`(B - log ‖f c‖) / log (R / r)`. -/
theorem divisor_sum_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {r R B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfc : f c ≠ 0)
    (havg : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) c R ≤ B) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall c r)) u : ℤ) : ℝ))
      ≤ (B - Real.log ‖f c‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall hrR.le
  have hlogpos : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr]; exact hrR)
  -- The divisor of `f` on the larger ball is nonnegative.
  have dR_nonneg : ∀ u : ℂ,
      (0 : ℝ) ≤ ((MeromorphicOn.divisor f (Metric.closedBall c R)) u : ℝ) := by
    intro u
    have h' : (0 : ℤ) ≤ (MeromorphicOn.divisor f (Metric.closedBall c R)) u :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u
    exact_mod_cast h'
  -- Move `log (R/r)` to the left-hand side.
  rw [le_div_iff₀ hlogpos, finsum_mul]
  -- It suffices to compare with the Jensen sum for the larger ball.
  refine le_trans ?_ (finsum_divisor_mul_log_le hR hf hfc havg)
  refine finsum_le_finsum' ?_ ?_ fun u => ?_
  · -- finite support of the left-hand sum
    refine (MeromorphicOn.divisor f (Metric.closedBall c r)).finiteSupport
      (isCompact_closedBall c r) |>.subset ?_
    rintro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    exact fun h => hx (by simp [h])
  · -- finite support of the right-hand sum
    refine (MeromorphicOn.divisor f (Metric.closedBall c R)).finiteSupport
      (isCompact_closedBall c R) |>.subset ?_
    rintro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    exact fun h => hx (by simp [h])
  · -- pointwise comparison
    by_cases h1 : u ∈ Metric.closedBall c R
    · by_cases h2 : u ∈ Metric.closedBall c r
      · -- `u` lies in the small ball: the two divisors agree there
        have hdrR : (MeromorphicOn.divisor f (Metric.closedBall c r)) u
            = (MeromorphicOn.divisor f (Metric.closedBall c R)) u := by
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono hsub) h2,
              MeromorphicOn.AnalyticOnNhd.divisor_apply hf h1]
        by_cases h3 : u = c
        · -- at the center the divisor vanishes since `f c ≠ 0`
          rw [h3]
          have hzero : (MeromorphicOn.divisor f (Metric.closedBall c r)) c = 0 := by
            rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono hsub)
                  (by simp [Metric.mem_closedBall, hr.le]),
                (hf c (by simp [Metric.mem_closedBall, hR.le])).analyticOrderAt_eq_zero.mpr hfc]
            simp
          rw [hzero]
          simp [Real.log_zero]
        · -- otherwise the log factor for the larger ball dominates
          rw [hdrR]
          apply mul_le_mul_of_nonneg_left ?_ (dR_nonneg u)
          apply Real.log_le_log (by positivity)
          have hcu_pos : 0 < ‖c - u‖ := by
            rw [norm_pos_iff]
            exact sub_ne_zero.mpr (Ne.symm h3)
          have hcu_le : ‖c - u‖ ≤ r := by
            simpa [Metric.mem_closedBall, dist_eq_norm'] using h2
          rw [div_le_div_iff₀ hr hcu_pos]
          exact mul_le_mul_of_nonneg_left hcu_le hR.le
      · -- `u` is in the large ball but not the small one: left term is `0`, right term nonneg
        have hdr0 : (MeromorphicOn.divisor f (Metric.closedBall c r)) u = 0 :=
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h2
        rw [hdr0, Int.cast_zero, zero_mul]
        refine mul_nonneg (dR_nonneg u) ?_
        have hcu_le_R : ‖c - u‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm'] using h1
        have hcu_gt : r < ‖c - u‖ := by
          simpa [Metric.mem_closedBall, dist_eq_norm'] using h2
        have hcu_pos : 0 < ‖c - u‖ := hr.trans hcu_gt
        apply Real.log_nonneg
        rw [one_le_div hcu_pos]
        exact hcu_le_R
    · -- `u` is outside the large ball: both terms vanish
      have h2 : u ∉ Metric.closedBall c r := fun h => h1 (hsub h)
      have hdr0 : (MeromorphicOn.divisor f (Metric.closedBall c r)) u = 0 :=
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h2
      have hdR0 : (MeromorphicOn.divisor f (Metric.closedBall c R)) u = 0 :=
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h1
      rw [hdr0, hdR0, Int.cast_zero, zero_mul, zero_mul]

end Commons.Analysis.Complex
