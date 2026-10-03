/-
# The amplitude (inverse-Fourier) form of the convolution identity

`Work.KMTPlan.A6.fourierInv_mul_eq_fourierInv_conv`: the product of two inverse Fourier
transforms is the inverse Fourier transform of the convolution of their amplitudes,

  `𝓕⁻A · 𝓕⁻B = 𝓕⁻(A * B)`,   `(A * B)(ζ) = ∫ η, A η · B (ζ - η)`.

This is the step that makes the amplitude of a *product* of two band-limited convolutions
explicit (the amplitude of the product is the convolution of the amplitudes), which is what the
mod-`Q` decomposition of the §8 model slice (`Work.KMTPlan.A6.modQ_decomposition_of_fourierInv`)
consumes.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped FourierTransform Convolution

/-- **`𝓕⁻A · 𝓕⁻B = 𝓕⁻(A * B)`** for `L¹` amplitudes `A, B`. -/
theorem fourierInv_mul_eq_fourierInv_conv (A B : ℝ → ℂ)
    (hA : MeasureTheory.Integrable A) (hB : MeasureTheory.Integrable B) (x : ℝ) :
    FourierTransformInv.fourierInv A x * FourierTransformInv.fourierInv B x
      = FourierTransformInv.fourierInv (fun ζ : ℝ => ∫ η : ℝ, A η * B (ζ - η)) x := by
  have hAneg : MeasureTheory.Integrable (fun ξ : ℝ => A (-ξ)) := hA.comp_neg
  have hBneg : MeasureTheory.Integrable (fun ξ : ℝ => B (-ξ)) := hB.comp_neg
  have hconv : (fun ζ : ℝ => ∫ η : ℝ, A η * B (-ζ - η))
      = convolution (fun ξ : ℝ => A (-ξ)) (fun ξ : ℝ => B (-ξ))
          (ContinuousLinearMap.lsmul ℂ ℂ) volume := by
    funext ζ
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hstep : (∫ t : ℝ, A (-t) * B (-(ζ - t))) = ∫ t : ℝ, A (-t) * B (-ζ + t) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only [show -(ζ - t) = -ζ + t by ring]
    rw [hstep, ← MeasureTheory.integral_neg_eq_self (f := fun u : ℝ => A u * B (-ζ - u))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [show -ζ - -t = -ζ + t by ring]
  have hmain : FourierTransform.fourier (fun ξ : ℝ => A (-ξ)) x
        * FourierTransform.fourier (fun ξ : ℝ => B (-ξ)) x
      = FourierTransform.fourier (fun ξ : ℝ => ∫ η : ℝ, A η * B (-ξ - η)) x := by
    rw [hconv, Real.fourier_smul_convolution_eq hAneg hBneg x, smul_eq_mul]
  rw [Real.fourierInv_eq_fourier_comp_neg A, Real.fourierInv_eq_fourier_comp_neg B,
    Real.fourierInv_eq_fourier_comp_neg (fun ζ : ℝ => ∫ η : ℝ, A η * B (ζ - η))]
  exact hmain

end Work.KMTPlan.A6
