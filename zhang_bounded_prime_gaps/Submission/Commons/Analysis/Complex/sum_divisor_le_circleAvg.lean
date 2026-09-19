import Mathlib.Analysis.Complex.JensenFormula

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology
open scoped Real BigOperators

noncomputable section

namespace Commons.Analysis.Complex

/-- **Jensen's inequality with a circle-average bound**: if `A` is an upper bound for the circle
average of `log ‖f‖` on the circle of radius `|R|` around `c`, then the number of zeros of `f`
(with multiplicity, as a divisor sum) in the ball of radius `|r| < |R|` is at most
`(A - log ‖f c‖) / log (R/r)`.  (The "average" refinement of `AnalyticOnNhd.sum_divisor_le`.) -/
theorem sum_divisor_le_circleAvg {c : ℂ} {r R A : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0)
    (havg : Real.circleAverage (fun x : ℂ => Real.log ‖f x‖) c R ≤ A) :
    ∑ᶠ u, MeromorphicOn.divisor f (closedBall c |r|) u ≤ (A - Real.log ‖f c‖) / Real.log (R / r) := by
  -- Push the coerssion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) u : ℝ)
  · exact map_finsum (Int.castRingHom ℝ)
      ((divisor _ _).finiteSupport <| isCompact_closedBall ..) |>.le
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hrR : 1 < |R / r| := by simpa [abs_div, one_lt_div r_pos]
  suffices ∑ᶠ u, divisor f (closedBall c |r|) u * Real.log (R / r) ≤ A - Real.log ‖f c‖ by
    rwa [← finsum_mul, ← le_div_iff₀] at this
    simpa using log_pos hrR
  have jensen := h₁f.circleAverage_log_norm (abs_ne_zero.mp (by linarith)) h₂f
  calc
  -- Bound by the sum from Jensen's formula
  (∑ᶠ u, divisor f (closedBall c |r|) u * Real.log (R / r))
      ≤ ∑ᶠ u, ((divisor f (closedBall c |R|)) u) * Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_le_finsum' ?_ ?_ fun u ↦ ?_
    · exact (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · exact (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · -- Core bound: estimate the summand by splitting on which ball u is in
      by_cases h1 : u ∈ closedBall c |R|
      · by_cases h2 : u ∈ closedBall c |r|
        · --In the smaller ball: the divisors agree and we bound the log factor
          simp only [(h₁f.mono (closedBall_subset_closedBall r_lt_R.le)), h2,
            AnalyticOnNhd.divisor_apply, h₁f, h1]
          by_cases! h3 : u = c --Need to use the divisor is 0 at c rather than comparing the logs
          · rw [h3, (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]
            simp
          simp +singlePass only [← log_abs]
          gcongr 2
          · simp
          · have : ‖c - u‖ ≠ 0 := by simpa [sub_eq_zero] using h3.symm
            simpa [field, abs_div, r_pos.trans r_lt_R, dist_eq_norm'] using h2
        · --In the larger ball but not the smaller so LHS is 0 and RHS nonnegative
          simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
          apply log_abs _ ▸ log_nonneg
          simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
          have : ‖c - u‖ ≠ 0 := (r_pos.trans h2).ne'
          simpa [field]
      · --Outside the larger ball so both sides are 0
        have : u ∉ closedBall c |r| := by
          simp_all
          linarith
        simp [h1, this]
  _ ≤ A - Real.log ‖f c‖ := by linarith --Uses jensen and havg

end Commons.Analysis.Complex
