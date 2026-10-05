import Mathlib

namespace Work.RPCore.Flow

open scoped ContDiff

/-- The antiderivative `t ↦ ∫₀ᵗ c` of a smooth function `c : ℝ → ℝ` is smooth.

This uses the characterisation of `C^∞` functions in one dimension as those that are
differentiable with a `C^∞` derivative: the fundamental theorem of calculus gives
`deriv (fun t => ∫ s in 0..t, c s) = c`, and `c` is smooth by hypothesis. -/
theorem antideriv_contDiff (c : ℝ → ℝ) (hc : ContDiff ℝ (↑(⊤ : ℕ∞)) c) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => ∫ s in (0 : ℝ)..t, c s) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hc.continuous, ?_⟩
  have hderiv : deriv (fun t => ∫ s in (0 : ℝ)..t, c s) = c := by
    funext t
    exact intervalIntegral.deriv_integral_right (hc.continuous.intervalIntegrable 0 t)
      hc.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuous.continuousAt
  rw [hderiv]
  exact hc

end Work.RPCore.Flow
