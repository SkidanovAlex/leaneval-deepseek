import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open scoped FourierTransform
open MeasureTheory

theorem integrable_fourier_mul_fourier_neg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {f : V → ℂ} (hf : MeasureTheory.Integrable f) (g : SchwartzMap V ℂ) : MeasureTheory.Integrable (fun p : V => FourierTransform.fourier f p * FourierTransform.fourier (g : V → ℂ) (-p)) := by
  have hg : MeasureTheory.Integrable (fun p : V => 𝓕 (g : V → ℂ) (-p)) := by
    have h : (fun p : V => 𝓕 (g : V → ℂ) (-p)) = 𝓕⁻ (g : V → ℂ) := by
      funext p
      rw [Real.fourierInv_eq_fourier_neg]
    rw [h, ← SchwartzMap.fourierInv_coe g]
    exact (𝓕⁻ g).integrable
  have hcont : Continuous (fun p : V => 𝓕 f p) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hbound : ∀ᵐ a : V, ‖𝓕 f a‖ ≤ ∫ x : V, ‖f x‖ :=
    Filter.Eventually.of_forall fun a =>
      VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ V) f a
  have hmain : MeasureTheory.Integrable (fun p : V => 𝓕 f p • 𝓕 (g : V → ℂ) (-p)) :=
    hg.bdd_smul (∫ x : V, ‖f x‖) hcont.aestronglyMeasurable hbound
  simpa only [smul_eq_mul] using hmain

end Commons.Analysis.Fourier