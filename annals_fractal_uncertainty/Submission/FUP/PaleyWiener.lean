import Submission.FUP.BMReduction
import Submission.Commons.Analysis.Fourier.fourier_Lp_ae_eq_zero_of_entire_growth

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators FourierTransform

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-- The Euclidean norm of the imaginary part is the `ℓ²`-norm of the coordinatewise imaginary
parts. -/
lemma norm_imVec_eq (z : ℂᵈ) : ‖imVec z‖ = Real.sqrt (∑ i, (z i).im ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (imVec z))]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.norm_eq_abs, sq_abs]

/-- **Cohen's Theorem 2.3 / Hörmander's Theorem 7.3.1 (the direction used in §2).**
An entire function of exponential type `σ` whose restriction to `ℝᵈ` is in `L²` has Fourier
transform supported in the closed ball of radius `σ/(2π)`. -/
theorem paley_wiener_statement_proof : paley_wiener_statement (d := d) := by
  intro F hFd σ A hσ hA hgrowth g hg
  have hgr : ∀ z : ℂᵈ, ‖F z‖ ≤ A * Real.exp (σ * Real.sqrt (∑ i, (z i).im ^ 2)) := by
    intro z
    have h := hgrowth z
    rwa [norm_imVec_eq z] at h
  have hmain := Commons.Analysis.Fourier.fourier_Lp_ae_eq_zero_of_entire_growth
    (d := d) σ A hσ hA F hFd hgr g hg
  filter_upwards [hmain] with ξ hξ hξnot
  exact hξ (by
    rw [Metric.mem_closedBall, dist_zero_right] at hξnot
    exact not_le.mp hξnot)

end Submission.FUP
