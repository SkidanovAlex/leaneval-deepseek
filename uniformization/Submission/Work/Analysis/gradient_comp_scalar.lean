import Mathlib

namespace Work.Analysis

/-- Chain rule for the real gradient of a scalar composition `Θ ∘ u`, where
`u : ℂ → ℝ` and `Θ : ℝ → ℝ`: the gradient of `Θ ∘ u` is `deriv Θ (u z)` times the
gradient of `u`. -/
theorem gradient_comp_scalar {u : ℂ → ℝ} {Θ : ℝ → ℝ} {z : ℂ}
    (hΘ : DifferentiableAt ℝ Θ (u z)) (hu : DifferentiableAt ℝ u z) :
    gradient (fun w => Θ (u w)) z = deriv Θ (u z) • gradient u z := by
  have hΘ' : HasFDerivAt Θ (fderiv ℝ Θ (u z)) (u z) := hΘ.hasFDerivAt
  have hu' : HasFDerivAt u (fderiv ℝ u z) z := hu.hasFDerivAt
  have hchain := HasFDerivAt.comp z hΘ' hu'
  have key : (InnerProductSpace.toDual ℝ ℂ) (deriv Θ (u z) • gradient u z)
      = (fderiv ℝ Θ (u z)).comp (fderiv ℝ u z) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    rw [real_inner_smul_left, inner_gradient_left, fderiv_eq_smul_deriv, smul_eq_mul, mul_comm]
  have : HasGradientAt (fun w => Θ (u w)) (deriv Θ (u z) • gradient u z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hchain.congr_fderiv key.symm
  exact this.gradient

end Work.Analysis
