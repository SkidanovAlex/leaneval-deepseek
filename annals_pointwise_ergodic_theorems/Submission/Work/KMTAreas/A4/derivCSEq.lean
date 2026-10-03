/-
# The derivative of a convolution of Schwartz functions

`Work.KMTAreas.A4.cS u v` is the convolution `u ⋆ v` of two complex Schwartz functions on `ℝ`
(`Submission/Work/KMTAreas/A4/offDecayDefs.lean`).  Here we record that the one-dimensional
derivative `SchwartzMap.derivCLM ℝ ℂ` commutes with convolution in the sense that

`(cS f g)' = cS f' g`,

i.e. the derivative of the convolution may be taken on the first factor.  (Equivalently, together
with the commutativity `cS f g = cS g f` of the convolution, the derivative may be taken on either
factor.)

The proof goes through the Fourier transform, which exchanges the pointwise product `mS` with the
convolution `cS` (`fourier_cS`).  The key input is the classical formula
`𝓕 (f') = fun ξ ↦ 2πiξ • 𝓕 f ξ` for an integrable differentiable `f` with integrable derivative
(`Real.fourier_deriv`), applied to the Schwartz functions `f`, `g` and `cS f g`.  Finally, since
`𝓕` is a bijection of Schwartz space, equality after Fourier transform is equality.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offDecayDefs

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

namespace Work.KMTAreas.A4

/-- The classical formula for the Fourier transform of the derivative, applied to a complex
Schwartz function: `𝓕 (h') ξ = 2πiξ • 𝓕 h ξ`. -/
theorem fourier_derivCLM_apply (h : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (𝓕 (SchwartzMap.derivCLM ℝ ℂ h)) ξ
      = (2 * ↑Real.pi * Complex.I * ↑ξ) • (𝓕 h) ξ := by
  have hcoe : (deriv (⇑h : ℝ → ℂ)) = ⇑(SchwartzMap.derivCLM ℝ ℂ h) := by
    funext x
    exact (SchwartzMap.derivCLM_apply ℝ h x).symm
  have hint : Integrable (deriv (⇑h : ℝ → ℂ)) := by
    rw [hcoe]
    exact (SchwartzMap.derivCLM ℝ ℂ h).integrable
  have key := Real.fourier_deriv (E := ℂ) (f := (⇑h : ℝ → ℂ)) h.integrable h.differentiable hint
  calc (𝓕 (SchwartzMap.derivCLM ℝ ℂ h)) ξ
      = (𝓕 (⇑(SchwartzMap.derivCLM ℝ ℂ h)) : ℝ → ℂ) ξ := by rw [SchwartzMap.fourier_coe]
    _ = (𝓕 (deriv (⇑h : ℝ → ℂ))) ξ := by rw [hcoe]
    _ = (2 * ↑Real.pi * Complex.I * ↑ξ) • (𝓕 (⇑h : ℝ → ℂ)) ξ := congrFun key ξ
    _ = (2 * ↑Real.pi * Complex.I * ↑ξ) • (𝓕 h) ξ := by rw [SchwartzMap.fourier_coe]

/-- The Fourier transform of a Schwartz function is injective (it is a bijection of Schwartz
space, with inverse the inverse Fourier transform). -/
theorem fourier_injective :
    Function.Injective (FourierTransform.fourier : SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ) :=
  fun a b hab => by
    have ha : FourierTransformInv.fourierInv (FourierTransform.fourier a) = a :=
      FourierPair.fourierInv_fourier_eq a
    have hb : FourierTransformInv.fourierInv (FourierTransform.fourier b) = b :=
      FourierPair.fourierInv_fourier_eq b
    rw [← ha, hab, hb]

/-- The derivative of the convolution of two complex Schwartz functions on `ℝ` may be taken on the
first factor: `(cS f g)' = cS f' g`. -/
theorem derivCSEq (f g : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℝ ℂ (Work.KMTAreas.A4.cS f g)
      = Work.KMTAreas.A4.cS (SchwartzMap.derivCLM ℝ ℂ f) g := by
  apply fourier_injective
  ext ξ
  have h1 : (𝓕 (SchwartzMap.derivCLM ℝ ℂ (cS f g))) ξ
      = (2 * ↑Real.pi * Complex.I * ↑ξ) • ((𝓕 f) ξ * (𝓕 g) ξ) := by
    rw [fourier_derivCLM_apply (cS f g) ξ, fourier_cS f g, mS_apply]
  have h2 : (𝓕 (cS (SchwartzMap.derivCLM ℝ ℂ f) g)) ξ
      = ((2 * ↑Real.pi * Complex.I * ↑ξ) • (𝓕 f) ξ) * (𝓕 g) ξ := by
    rw [fourier_cS (SchwartzMap.derivCLM ℝ ℂ f) g, mS_apply, fourier_derivCLM_apply f ξ]
  rw [h1, h2, smul_eq_mul]
  ring

end Work.KMTAreas.A4
