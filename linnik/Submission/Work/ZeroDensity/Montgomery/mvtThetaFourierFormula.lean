import Mathlib
import Submission.Work.ZeroDensity.Montgomery.mvtDefs

/-!
# The Fourier transform of the spreading kernel `Θ_δ`

This file proves `Work.ZeroDensity.Montgomery.mvtThetaFourierFormula`, the identity

`𝓕 Θ_δ (ξ) = ‖ψ (δ ξ)‖²`,

where `Θ_δ = ρ_δ ⋆ \overline{ρ_δ(-·)}` is the spreading kernel (`mvtTheta`), `ρ_δ` is the rescaled
bump (`mvtRhoDeltaC`), and `ψ = 𝓕 ρ` (`mvtPsi`), `δ = mvtDelta S`.

The proof is the classical chain of Fourier rules on `ℝ`:

* scaling: `𝓕 (f (·/c)) = c • 𝓕 f (c ·)` for `c > 0` (`mvtFourier_comp_div`), giving
  `𝓕 ρ_δ (ξ) = ψ (δ ξ)` (`mvtRhoDeltaC_fourier`);
* reflection and conjugation: `𝓕 (star ∘ f ∘ neg) = star ∘ 𝓕 f` (`mvtFourier_star_neg`);
* the convolution theorem `𝓕 (f ⋆ g) = 𝓕 f · 𝓕 g` (`Real.fourier_mul_convolution_eq`),

after which `ψ (δ ξ) · star (ψ (δ ξ)) = ‖ψ (δ ξ)‖²` (`Complex.mul_conj`).
-/

open scoped FourierTransform ComplexConjugate
open MeasureTheory Filter

namespace Work.ZeroDensity.Montgomery

/-- **Scaling of the Fourier transform.** For `c > 0`, `𝓕 (fun y => f (y / c)) = c • 𝓕 f (c ·)`.

Proved directly from the integral definition with the change of variables `y = c u`
(`Measure.integral_comp_mul_left`). -/
lemma mvtFourier_comp_div (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun y => f (y / c)) ξ = c • 𝓕 f (c * ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hcomp : (∫ u : ℝ, 𝐞 (-((c * u) * ξ)) • f ((c * u) / c))
      = ∫ u : ℝ, 𝐞 (-(u * (c * ξ))) • f u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    beta_reduce
    rw [mul_div_cancel_left₀ u hc.ne', show -((c * u) * ξ) = -(u * (c * ξ)) by ring]
  have h := Measure.integral_comp_mul_left (fun y : ℝ => 𝐞 (-(y * ξ)) • f (y / c)) c
  rw [abs_of_pos (inv_pos.mpr hc)] at h
  rw [hcomp] at h
  rw [h, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- **Reflection-conjugation rule.** `𝓕 (fun y => star (f (-y))) = star (𝓕 f)`.

From the integral definition, using `integrable`-free `integral_conj`, the change of variables
`y ↦ -y` (`integral_neg_eq_self`) and `star (𝐞 u) = 𝐞 (-u)` (`Circle.star_addChar`). -/
lemma mvtFourier_star_neg (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun y => star (f (-y))) ξ = star (𝓕 f ξ) := by
  rw [Real.fourier_real_eq (f := fun y => star (f (-y))), Real.fourier_real_eq (f := f)]
  have hconj : star (∫ v, 𝐞 (-(v * ξ)) • f v) = ∫ v, star (𝐞 (-(v * ξ)) • f v) :=
    (integral_conj (μ := volume) (f := fun v => 𝐞 (-(v * ξ)) • f v)).symm
  rw [hconj]
  rw [← MeasureTheory.integral_neg_eq_self (fun y => star (𝐞 (-(y * ξ)) • f y)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [show -((-y) * ξ) = y * ξ by ring]
  simp only [Circle.smul_def, smul_eq_mul, star_mul, Circle.star_addChar]
  ring

/-- `𝓕 ρ_δ = ψ (δ ξ)`, i.e. `𝓕 (mvtRhoDeltaC S) ξ = mvtPsi (mvtDelta S * ξ)`. -/
lemma mvtRhoDeltaC_fourier (S : ℝ) (hS : 0 < S) (ξ : ℝ) :
    𝓕 (mvtRhoDeltaC S) ξ = mvtPsi (mvtDelta S * ξ) := by
  have hd : 0 < mvtDelta S := mvtDelta_pos hS
  have hfun : mvtRhoDeltaC S
      = fun y => (((mvtDelta S)⁻¹ : ℝ) : ℂ) * mvtRhoC (y / mvtDelta S) := by
    funext y; simp [mvtRhoDeltaC]
  rw [hfun]
  have h1 : 𝓕 (fun y => (((mvtDelta S)⁻¹ : ℝ) : ℂ) * mvtRhoC (y / mvtDelta S)) ξ
      = (((mvtDelta S)⁻¹ : ℝ) : ℂ) * 𝓕 (fun y => mvtRhoC (y / mvtDelta S)) ξ := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h1, mvtFourier_comp_div mvtRhoC hd ξ, mvtPsi, Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hd.ne', Complex.ofReal_one, one_mul]

theorem mvtThetaFourierFormula (S : ℝ) (hS : 0 < S) (ξ : ℝ) :
    FourierTransform.fourier (mvtTheta S) ξ = ((‖mvtPsi (mvtDelta S * ξ)‖ ^ 2 : ℝ) : ℂ) := by
  have hf1 : Integrable (mvtRhoDeltaC S) := mvtRhoDeltaC_integrable S hS
  have hf2 : Integrable (fun y => star (mvtRhoDeltaC S (-y))) := by
    have h := (LinearIsometryEquiv.integrable_comp_iff (RCLike.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ)).2
      (hf1.comp_neg)
    simpa [RCLike.conjLIE_apply] using h
  rw [mvtTheta, Real.fourier_mul_convolution_eq hf1 hf2 ξ,
    mvtRhoDeltaC_fourier S hS ξ, mvtFourier_star_neg (mvtRhoDeltaC S) ξ,
    mvtRhoDeltaC_fourier S hS ξ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Work.ZeroDensity.Montgomery
