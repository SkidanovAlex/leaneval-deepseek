import Mathlib
import Submission.Work.Kernels.ModerateGrowth

namespace Work.CKFinal

open UpperHalfPlane

/-! ## A two-term polynomial bound for the scale `S τ = 1 + (im τ)⁻¹ + ‖τ‖`

The scale `Work.Kernels.scale τ = 1 + (im τ)⁻¹ + ‖(τ : ℂ)‖` controls moderate growth of
holomorphic functions on `ℍ`.  For the growth estimates of the interpolation basis one
needs to dominate a *fixed power* of this scale by a two-term expression
`α * (im τ)^(-β) + γ * ‖(τ : ℂ)‖^δ` in which the factors `(im τ)⁻¹` and `‖τ‖` appear
separately (each with its own exponent and coefficient).  Since both are `≤ max` and
`1 ≤ max`, the scale is at most `3 * max`, and a `max` split gives the two terms.
-/

/-- The scale is dominated by `3 * max ((im τ)⁻¹) ‖τ‖`, and `1 ≤ max ((im τ)⁻¹) ‖τ‖`. -/
private lemma one_le_max_inv_im_norm (τ : UpperHalfPlane) :
    1 ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := by
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  obtain ⟨h1, h2⟩ := hlt
  have hy : 1 < τ.im := by
    rcases (inv_lt_one_iff₀.mp h1) with h | h
    · exact absurd h (not_le.mpr τ.im_pos)
    · exact h
  have hle : τ.im ≤ ‖(τ : ℂ)‖ := Work.Kernels.im_le_coe_norm τ
  linarith

/-- The plumbing estimate: a fixed nonnegative power of the scale is bounded by a
two-term expression with *separate* exponents on `(im τ)⁻¹` and on `‖τ‖`. -/
theorem scale_plumbing (N : ℝ) (hN : 0 ≤ N) :
    ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ τ : UpperHalfPlane, (Work.Kernels.scale τ) ^ N ≤ α * τ.im ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ := by
  refine ⟨3 ^ N, N, 3 ^ N, N, Real.rpow_nonneg (by norm_num) N, hN,
    Real.rpow_nonneg (by norm_num) N, hN, fun τ => ?_⟩
  have ha : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
  have hb : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hm0 : 0 ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := le_trans ha (le_max_left _ _)
  have hm1 : 1 ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := one_le_max_inv_im_norm τ
  have hscale : Work.Kernels.scale τ ≤ 3 * max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := by
    unfold Work.Kernels.scale
    linarith [le_max_left ((τ.im)⁻¹) ‖(τ : ℂ)‖, le_max_right ((τ.im)⁻¹) ‖(τ : ℂ)‖, hm1]
  have h1 : (Work.Kernels.scale τ) ^ N ≤ (3 * max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N :=
    Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hscale hN
  have h2 : (3 * max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N
      = 3 ^ N * (max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N := Real.mul_rpow (by norm_num) hm0
  have h3 : (max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N ≤ (τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N := by
    rcases le_total ((τ.im)⁻¹) ‖(τ : ℂ)‖ with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg ha N)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hb N)
  have hinv : (τ.im)⁻¹ ^ N = τ.im ^ (-N) :=
    (Real.inv_rpow τ.im_pos.le N).trans (Real.rpow_neg τ.im_pos.le N).symm
  calc (Work.Kernels.scale τ) ^ N ≤ (3 * max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N := h1
    _ = 3 ^ N * (max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N := h2
    _ ≤ 3 ^ N * ((τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) N)
    _ = 3 ^ N * τ.im ^ (-N) + 3 ^ N * ‖(τ : ℂ)‖ ^ N := by rw [hinv]; ring

end Work.CKFinal
