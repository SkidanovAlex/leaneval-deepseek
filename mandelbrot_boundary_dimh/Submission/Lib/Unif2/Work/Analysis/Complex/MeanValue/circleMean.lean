import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.MeanValue.circleAux

/-!
# The circle mean value inequality for `|u|²`

For a function `u : ℂ → ℂ` complex differentiable on the disc `ball c r` and continuous on its
closure, the mean value property applied to the *holomorphic* function `u ^ 2` gives
`u c ^ 2 = circleAverage (u ^ 2) c r`; taking norms and using
`‖circleAverage f c r‖ ≤ circleAverage ‖f‖ c r` gives

  `2 π ‖u c‖² ≤ ∫_0^{2π} ‖u (c + r e^{i θ})‖² dθ`.

This is the first (and only) input of the area mean value inequality
`norm_sq_mul_le_integral_ball`, which in turn produces the sup-norm bound for holomorphic functions
in terms of their weighted `L²` norm (the `L² → L^∞` step of the `∂̄`/Hörmander route to the
divisor theorem).
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.MeanValue

/-- The norm of a circle average is at most the circle average of the norm. -/
lemma norm_circleAverage_le_circleAverage_norm {f : ℂ → ℂ} {c : ℂ} {R : ℝ} :
    ‖Real.circleAverage f c R‖ ≤ Real.circleAverage (fun z => ‖f z‖) c R := by
  rw [Real.circleAverage_def, Real.circleAverage_def, norm_smul,
    Real.norm_of_nonneg (by positivity), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
    (by positivity)

/-- **Circle mean value inequality for `|u|²`.**  For `u` complex differentiable on the open disc
of centre `c` and radius `r > 0` and continuous on its closure. -/
theorem circle_mean_value_sq {u : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hu : DiffContOnCl ℂ u (Metric.ball c r)) :
    2 * Real.pi * ‖u c‖ ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖u (circleMap c r θ)‖ ^ 2 := by
  have hsq : DiffContOnCl ℂ (fun z => u z ^ 2) (Metric.ball c r) :=
    ⟨hu.1.pow 2, hu.2.pow 2⟩
  have hmv : Real.circleAverage (fun z => u z ^ 2) c r = u c ^ 2 :=
    DiffContOnCl.circleAverage (R := r) (by simpa [abs_of_pos hr] using hsq)
  have hci : CircleIntegrable (fun z => u z ^ 2) c r := by
    refine ContinuousOn.circleIntegrable' (f := fun z => u z ^ 2) (R := r) ?_
    refine hsq.2.mono ?_
    rw [abs_of_pos hr, closure_ball c (ne_of_gt hr)]
    exact Metric.sphere_subset_closedBall
  have key : ‖u c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖u z‖ ^ 2) c r := by
    have h := norm_circleAverage_le_circleAverage_norm (f := fun z => u z ^ 2) (c := c) (R := r)
    rw [hmv] at h
    simpa [norm_pow] using h
  rw [Real.circleAverage_def, smul_eq_mul] at key
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  calc 2 * Real.pi * ‖u c‖ ^ 2
      ≤ 2 * Real.pi *
          ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖u (circleMap c r θ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left key (le_of_lt h2pi)
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖u (circleMap c r θ)‖ ^ 2 := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2pi), one_mul]

end Work.Analysis.Complex.MeanValue
