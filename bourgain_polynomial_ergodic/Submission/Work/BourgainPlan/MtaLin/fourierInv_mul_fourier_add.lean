import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs

/-!
# Linearity of `𝓕⁻ (m · 𝓕 ·)` in the argument

For integrable `m, f, g : ℝ → ℂ` the map
`f ↦ 𝓕⁻ (fun ξ => m ξ * 𝓕 f ξ)`
is additive.  The proof is pointwise:

* `𝓕 (f + g) = 𝓕 f + 𝓕 g` (additivity of the Fourier integral of `L¹` functions);
* hence `m · 𝓕 (f + g) = m · 𝓕 f + m · 𝓕 g` pointwise;
* the products `m · 𝓕 f` and `m · 𝓕 g` are integrable: `𝓕 f` is bounded by `‖f‖₁`
  (`VectorFourier.norm_fourierIntegral_le_integral_norm`) and continuous, while `m` is integrable;
* the inverse Fourier transform of integrable functions is additive
  (`fourierInv_add_of_integrable`), being the integral of the (integrable) pullback `𝐞 (⟪·,x⟫) • ·`.
-/

namespace Work.BourgainPlan.MtaLin

open MeasureTheory
open scoped FourierTransform

/-- Additivity of the inverse Fourier transform on integrable functions: the integrand
`ξ ↦ 𝐞 (⟪ξ,x⟫) • A ξ` is integrable as soon as `A` is (`Real.fourierIntegral_convergent_iff`). -/
lemma fourierInv_add_of_integrable {A B : ℝ → ℂ} (hA : MeasureTheory.Integrable A)
    (hB : MeasureTheory.Integrable B) (x : ℝ) :
    FourierTransform.fourierInv (A + B) x
      = FourierTransform.fourierInv A x + FourierTransform.fourierInv B x := by
  rw [Real.fourierInv_eq (A + B) x, Real.fourierInv_eq A x, Real.fourierInv_eq B x]
  rw [show (fun v : ℝ => Real.fourierChar (inner ℝ v x) • (A + B) v)
        = (fun v : ℝ => Real.fourierChar (inner ℝ v x) • A v
            + Real.fourierChar (inner ℝ v x) • B v) from by
        funext v; simp only [Pi.add_apply, smul_add]]
  rw [MeasureTheory.integral_add]
  · simpa using (Real.fourierIntegral_convergent_iff (-x)).2 hA
  · simpa using (Real.fourierIntegral_convergent_iff (-x)).2 hB

theorem fourierInv_mul_fourier_add {m f g : ℝ → ℂ} (hm : MeasureTheory.Integrable m) (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) (x : ℝ) :
    FourierTransform.fourierInv (fun ξ : ℝ => m ξ * FourierTransform.fourier (f + g) ξ) x
      = FourierTransform.fourierInv (fun ξ : ℝ => m ξ * FourierTransform.fourier f ξ) x
        + FourierTransform.fourierInv (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) x := by
  -- additivity of the Fourier transform, pointwise
  have hfarith : ∀ ξ : ℝ,
      FourierTransform.fourier (f + g) ξ
        = FourierTransform.fourier f ξ + FourierTransform.fourier g ξ := by
    intro ξ
    rw [Real.fourier_eq (f + g) ξ, Real.fourier_eq f ξ, Real.fourier_eq g ξ]
    rw [show (fun v : ℝ => Real.fourierChar (-inner ℝ v ξ) • (f + g) v)
          = (fun v : ℝ => Real.fourierChar (-inner ℝ v ξ) • f v
              + Real.fourierChar (-inner ℝ v ξ) • g v) from by
          funext v; simp only [Pi.add_apply, smul_add]]
    rw [MeasureTheory.integral_add]
    · exact (Real.fourierIntegral_convergent_iff ξ).2 hf
    · exact (Real.fourierIntegral_convergent_iff ξ).2 hg
  -- `𝓕 f` is continuous and bounded by `‖f‖₁`
  have hcontf : Continuous (FourierTransform.fourier f) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hf
  have hboundf : ∀ ξ : ℝ, ‖FourierTransform.fourier f ξ‖ ≤ ∫ v : ℝ, ‖f v‖ := fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) f ξ
  have hcontg : Continuous (FourierTransform.fourier g) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hg
  have hboundg : ∀ ξ : ℝ, ‖FourierTransform.fourier g ξ‖ ≤ ∫ v : ℝ, ‖g v‖ := fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) g ξ
  -- the two products are integrable
  have hF : MeasureTheory.Integrable (fun ξ : ℝ => m ξ * FourierTransform.fourier f ξ) := by
    refine hm.mul_bdd (g := fun ξ => FourierTransform.fourier f ξ) (c := ∫ v : ℝ, ‖f v‖) ?_ ?_
    · exact hcontf.aestronglyMeasurable
    · filter_upwards with ξ
      exact hboundf ξ
  have hG : MeasureTheory.Integrable (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) := by
    refine hm.mul_bdd (g := fun ξ => FourierTransform.fourier g ξ) (c := ∫ v : ℝ, ‖g v‖) ?_ ?_
    · exact hcontg.aestronglyMeasurable
    · filter_upwards with ξ
      exact hboundg ξ
  -- identify the integrand of the left-hand side
  have hH : (fun ξ : ℝ => m ξ * FourierTransform.fourier (f + g) ξ)
      = (fun ξ : ℝ => m ξ * FourierTransform.fourier f ξ)
        + (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) := by
    funext ξ
    rw [Pi.add_apply, hfarith ξ]
    ring
  have hmain := fourierInv_add_of_integrable hF hG x
  rw [← hH] at hmain
  exact hmain

end Work.BourgainPlan.MtaLin
