/-
# The `L¹` norms of the rescaled cutoff and of its first two derivatives

For `x₀ δ : ℝ` the *rescaled cutoff* is `scaledBump x₀ δ = fun ξ ↦ η((ξ - x₀)/δ)`, where
`η = Work.KMTContract.kmtEta`.  Its first two derivatives are computed in
`scaledBump_derivs.lean`:

`(scaledBump x₀ δ)' ξ = (1/δ) η'((ξ - x₀)/δ)`,
`(scaledBump x₀ δ)'' ξ = (1/δ²) η''((ξ - x₀)/δ)`.

This module integrates the absolute values of those identities.  The change of variables
`ξ = x₀ + δ y` turns the `L¹` norm of the rescaled cutoff into `δ` times the `L¹` norm of `η`,
and it leaves the `L¹` norm of the derivative unchanged (the gain `δ⁻¹` from the chain rule
cancels the factor `δ` from the substitution); the second derivative gains a factor `δ⁻¹`.
The three constants `etaI0`, `etaI1`, `etaI2` of `Norms.lean` are exactly the `L¹` norms of
`η`, `η'` and `η''`, so the three integral identities are

* `∫ ξ, ‖scaledBump x₀ δ ξ‖ = δ * etaI0`,
* `∫ ξ, ‖(scaledBump x₀ δ)' ξ‖ = etaI1`,
* `∫ ξ, ‖(scaledBump x₀ δ)'' ξ‖ = etaI2 / δ`.

The only analytic ingredient is the affine change of variables on `ℝ` for the Lebesgue
integral (`integral_comp_sub_div`, proved from the translation invariance of Lebesgue measure
and the dilation rule `Measure.integral_comp_div`); it is stated for arbitrary `ℝ`-valued
functions, the non-integrable case being handled by the convention that such functions have
integral `0`.
-/
import Mathlib
import Submission.Work.KMTAreas.SupNorm.Norms
import Submission.Work.KMTAreas.SupNorm.scaledBump_derivs

set_option autoImplicit false

open MeasureTheory

namespace Work.KMTAreas.SupNorm

open Work.KMTContract

/-- **Affine change of variables for the Lebesgue integral on `ℝ`.**
For `δ > 0` and every `f : ℝ → ℝ`,
`∫ ξ, f ((ξ - x₀)/δ) = δ * ∫ y, f y`.

The Bochner integral of a non-integrable function is `0`, and the substitution preserves
(non-)integrability, so no hypothesis on `f` is needed. -/
theorem integral_comp_sub_div (f : ℝ → ℝ) (x₀ δ : ℝ) (hδ : 0 < δ) :
    (∫ ξ : ℝ, f ((ξ - x₀) / δ)) = δ * ∫ y : ℝ, f y := by
  rw [integral_sub_right_eq_self (fun y : ℝ => f (y / δ)) x₀]
  rw [Measure.integral_comp_div f δ, abs_of_pos hδ, smul_eq_mul]

/-- **The `L¹` norms of the rescaled cutoff and of its first two derivatives.**
For `δ > 0`,

* `∫ ‖scaledBump x₀ δ‖ = δ * etaI0`,
* `∫ ‖(scaledBump x₀ δ)'‖ = etaI1`,
* `∫ ‖(scaledBump x₀ δ)''‖ = etaI2 / δ`. -/
theorem scaledBump_norm_integrals {x₀ δ : ℝ} (hδ : 0 < δ) :
    (∫ ξ : ℝ, ‖Work.KMTAreas.SupNorm.scaledBump x₀ δ ξ‖) = δ * Work.KMTAreas.SupNorm.etaI0
    ∧ (∫ ξ : ℝ, ‖deriv (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖) = Work.KMTAreas.SupNorm.etaI1
    ∧ (∫ ξ : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖)
        = Work.KMTAreas.SupNorm.etaI2 / δ := by
  have hI0 : (∫ ξ : ℝ, ‖Work.KMTAreas.SupNorm.scaledBump x₀ δ ξ‖) = δ * etaI0 := by
    have h : (fun ξ : ℝ => ‖Work.KMTAreas.SupNorm.scaledBump x₀ δ ξ‖)
        = fun ξ : ℝ => ‖kmtEta ((ξ - x₀) / δ)‖ := by
      funext ξ; rfl
    rw [h, integral_comp_sub_div (fun y => ‖kmtEta y‖) x₀ δ hδ]
    rfl
  have hI1 : (∫ ξ : ℝ, ‖deriv (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖) = etaI1 := by
    have hpt : ∀ ξ : ℝ, ‖deriv (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖
        = (1 / δ) * ‖deriv kmtEta ((ξ - x₀) / δ)‖ := by
      intro ξ
      rw [Work.KMTAreas.SupNorm.scaledBump_deriv]
      simp only []
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hδ)]
    calc (∫ ξ : ℝ, ‖deriv (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖)
        = ∫ ξ : ℝ, (1 / δ) * ‖deriv kmtEta ((ξ - x₀) / δ)‖ :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = δ * ∫ y : ℝ, (1 / δ) * ‖deriv kmtEta y‖ :=
          integral_comp_sub_div (fun y => (1 / δ) * ‖deriv kmtEta y‖) x₀ δ hδ
      _ = δ * ((1 / δ) * ∫ y : ℝ, ‖deriv kmtEta y‖) := by
          rw [integral_const_mul]
      _ = etaI1 := by
          rw [show (∫ y : ℝ, ‖deriv kmtEta y‖) = etaI1 from rfl]
          field_simp
  have hI2 : (∫ ξ : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖)
      = etaI2 / δ := by
    have hpt : ∀ ξ : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖
        = (1 / δ ^ 2) * ‖iteratedDeriv 2 kmtEta ((ξ - x₀) / δ)‖ := by
      intro ξ
      rw [Work.KMTAreas.SupNorm.scaledBump_iteratedDeriv_two]
      simp only []
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc (∫ ξ : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.SupNorm.scaledBump x₀ δ) ξ‖)
        = ∫ ξ : ℝ, (1 / δ ^ 2) * ‖iteratedDeriv 2 kmtEta ((ξ - x₀) / δ)‖ :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = δ * ∫ y : ℝ, (1 / δ ^ 2) * ‖iteratedDeriv 2 kmtEta y‖ :=
          integral_comp_sub_div (fun y => (1 / δ ^ 2) * ‖iteratedDeriv 2 kmtEta y‖) x₀ δ hδ
      _ = δ * ((1 / δ ^ 2) * ∫ y : ℝ, ‖iteratedDeriv 2 kmtEta y‖) := by
          rw [integral_const_mul]
      _ = etaI2 / δ := by
          rw [show (∫ y : ℝ, ‖iteratedDeriv 2 kmtEta y‖) = etaI2 from rfl]
          field_simp
  exact ⟨hI0, hI1, hI2⟩

end Work.KMTAreas.SupNorm
