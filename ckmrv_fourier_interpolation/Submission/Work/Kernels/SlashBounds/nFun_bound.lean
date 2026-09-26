import Mathlib
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Kernels.SlashBounds

/-- An affine function of `z` with fixed coefficients grows at most linearly in `‖z‖`. -/
private lemma norm_affine_le (a b z : ℂ) :
    ‖a * z + b‖ ≤ (‖a‖ + ‖b‖) * (1 + ‖z‖) := by
  have h1 : ‖a * z + b‖ ≤ ‖a‖ * ‖z‖ + ‖b‖ := by
    calc ‖a * z + b‖ ≤ ‖a * z‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * ‖z‖ + ‖b‖ := by rw [norm_mul]
  have h2 : ‖a‖ * ‖z‖ + ‖b‖ ≤ (‖a‖ + ‖b‖) * (1 + ‖z‖) := by
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    have hz := norm_nonneg z
    nlinarith [mul_nonneg (add_nonneg ha hb) hz]
  linarith

lemma nFun_bound (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, ‖nFun γ (τ : ℂ)‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  refine ⟨‖(γ 0 0 : ℂ)‖ + ‖(γ 0 1 : ℂ)‖, by positivity, fun τ => ?_⟩
  rw [nFun_apply]
  exact norm_affine_le _ _ _

end Work.Kernels.SlashBounds
