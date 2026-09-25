import Mathlib

namespace Work.Beltrami

open MeasureTheory

/-- A continuous complex-valued function on `ℂ` which is bounded by `M` and vanishes outside the
closed ball of radius `R` around the origin is in `L²(ℂ)`. Indeed it agrees with a function
supported in a compact set (the closed ball), where it is dominated by the constant `‖M‖`, whose
`L²` norm is finite because the ball has finite Lebesgue measure. -/
theorem memLp_of_bounded_supported {R M : ℝ} {f : ℂ → ℂ} (hf : Continuous f)
    (hM : ∀ z, ‖f z‖ ≤ M) (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    MemLp f 2 volume := by
  set s := Metric.closedBall (0 : ℂ) R with hs_def
  have hs : MeasurableSet s := measurableSet_closedBall
  have hvol : volume s < ⊤ := (isCompact_closedBall (0 : ℂ) R).measure_lt_top
  -- The constant `‖M‖` on the compact ball is an `L²` function.
  have hg : MemLp (s.indicator fun _ => ((‖M‖ : ℝ) : ℂ)) 2 volume :=
    memLp_indicator_const 2 hs ((‖M‖ : ℝ) : ℂ) (Or.inr hvol.ne)
  -- Dominating `f` pointwise by that constant on the ball, and by `0` outside it.
  refine hg.mono hf.aestronglyMeasurable ?_
  filter_upwards with z
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz]
    have h : ‖((‖M‖ : ℝ) : ℂ)‖ = ‖M‖ := by
      have h' : ‖((‖M‖ : ℝ) : ℂ)‖ = |(‖M‖ : ℝ)| := by simp
      rw [h', abs_of_nonneg (norm_nonneg M)]
    rw [h]
    simpa using le_trans (hM z) (le_abs_self M)
  · -- Outside the ball we have `R < ‖z‖`, so `f z = 0` by hypothesis.
    rw [Set.indicator_of_notMem hz, norm_zero]
    simp only [hs_def, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    rw [hsupp z hz, norm_zero]

end Work.Beltrami
