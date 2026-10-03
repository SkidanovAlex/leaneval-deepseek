import Mathlib

/-
# Additivity of the (inverse) Fourier transform on `L¹(ℝ, ℂ)`

The inverse Fourier transform `𝓕⁻` on `ℝ → ℂ` is, by definition
(`Real.instFourierTransformInv`), the vector Fourier integral

`𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v`

where `𝐞` is the standard additive character.  When `f` and `g` are integrable the
integrands are integrable for every `w`, so additivity is the additivity of the
Bochner integral (`VectorFourier.fourierIntegral_add`).
-/

namespace Work.KMTAreas.SupNorm

open MeasureTheory

theorem fourierInv_add_of_integrable {f g : ℝ → ℂ} (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) :
    FourierTransformInv.fourierInv (f + g)
      = FourierTransformInv.fourierInv f + FourierTransformInv.fourierInv g := by
  change VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume (-(innerₗ ℝ)) (f + g)
      = VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume (-(innerₗ ℝ)) f
        + VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume (-(innerₗ ℝ)) g
  exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar (by fun_prop) hf hg

end Work.KMTAreas.SupNorm
