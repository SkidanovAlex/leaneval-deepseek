import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The inverse Fourier transform (with the `FourierTransformInv` notation instance for
functions `ℝ → ℂ`) is additive under subtraction of integrable functions: it is computed
by the (Bochner) integral `𝓕⁻ f x = ∫ v, 𝐞 ⟪v, x⟫ • f v`, and `integral_sub` applies since
the modulations `v ↦ 𝐞 ⟪v, x⟫ • hᵢ v` remain integrable when `hᵢ` is. -/
theorem fourierInv_sub_pt {h₁ h₂ : ℝ → ℂ} (h1 : MeasureTheory.Integrable h₁)
    (h2 : MeasureTheory.Integrable h₂) (x : ℝ) :
    FourierTransformInv.fourierInv (h₁ - h₂) x
      = FourierTransformInv.fourierInv h₁ x - FourierTransformInv.fourierInv h₂ x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Pi.sub_apply, smul_sub]
  · simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) (μ := volume) (-x)).2 h1
  · simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) (μ := volume) (-x)).2 h2

end Commons.Analysis.Fourier