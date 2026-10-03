import Mathlib.Analysis.Complex.MeanValue

open Set Metric
open scoped Topology Real

namespace Commons.Analysis.Complex

/-- **Triangle inequality for the real circle average.**  For a function
`f : ℂ → E` into a normed real space `E`:
`‖Real.circleAverage f c R‖ ≤ Real.circleAverage (fun z => ‖f z‖) c R`.
(Proof: `Real.circleAverage_def` writes both sides as
`(2π)⁻¹ • ∫ θ in 0..2π, f (circleMap c R θ)` resp. the integral of the
norms; the scalar `(2π)⁻¹ ≥ 0` leaves the norm/ordering unchanged, and
`intervalIntegral.norm_integral_le_integral_norm` bounds the norm of the
integral by the integral of the norms.) -/
theorem circleAverage_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (c : ℂ) (R : ℝ) :
    ‖Real.circleAverage f c R‖ ≤ Real.circleAverage (fun z : ℂ => ‖f z‖) c R := by
  rw [Real.circleAverage_def (f := f) (c := c) (R := R)]
  rw [Real.circleAverage_def (f := fun z : ℂ => ‖f z‖) (c := c) (R := R)]
  calc
    ‖(2 * Real.pi)⁻¹ • ∫ (θ : ℝ) in 0..2 * Real.pi, f (circleMap c R θ)‖
        = (2 * Real.pi)⁻¹ * ‖∫ (θ : ℝ) in 0..2 * Real.pi, f (circleMap c R θ)‖ := by
          rw [norm_smul]
          congr 1
          exact abs_of_nonneg (inv_nonneg.mpr (by positivity))
    _ ≤ (2 * Real.pi)⁻¹ * ∫ (θ : ℝ) in 0..2 * Real.pi, ‖f (circleMap c R θ)‖ := by
          exact mul_le_mul_of_nonneg_left
            (intervalIntegral.norm_integral_le_integral_norm (a := 0) (b := 2 * Real.pi)
              (by positivity : (0 : ℝ) ≤ 2 * Real.pi)) (by positivity)
    _ = (2 * Real.pi)⁻¹ • ∫ (θ : ℝ) in 0..2 * Real.pi, ‖f (circleMap c R θ)‖ := by
          simp

end Commons.Analysis.Complex
