import Mathlib
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Kernels.SlashBounds

/-- `j(γ,·)` is a linear function `z ↦ c z + d` with `c`, `d` bounded (indeed integral)
coefficients, hence is bounded by `(‖c‖ + ‖d‖) * (1 + ‖z‖)`. -/
lemma jFun_bound_upper (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, ‖jFun γ (τ : ℂ)‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  refine ⟨‖(γ 1 0 : ℂ)‖ + ‖(γ 1 1 : ℂ)‖, by positivity, fun τ => ?_⟩
  rw [jFun_apply]
  have h1 : ‖(γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)‖
      ≤ ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(γ 1 1 : ℂ)‖ := by
    have := norm_add_le ((γ 1 0 : ℂ) * (τ : ℂ)) (γ 1 1 : ℂ)
    rwa [norm_mul] at this
  have h2 : ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ ≤ ‖(γ 1 0 : ℂ)‖ * (1 + ‖(τ : ℂ)‖) := by
    nlinarith [norm_nonneg (τ : ℂ), norm_nonneg (γ 1 0 : ℂ)]
  have h3 : ‖(γ 1 1 : ℂ)‖ ≤ ‖(γ 1 1 : ℂ)‖ * (1 + ‖(τ : ℂ)‖) := by
    nlinarith [norm_nonneg (τ : ℂ), norm_nonneg (γ 1 1 : ℂ)]
  nlinarith [h1, h2, h3]

end Work.Kernels.SlashBounds
