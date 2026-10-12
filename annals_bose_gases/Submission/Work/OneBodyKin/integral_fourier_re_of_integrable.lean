import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

/-- The real part of the integral of the complex-valued momentum integrand
`p ↦ 𝓕(k)(p) · (‖𝓕(ψ)(p)‖² : ℂ)` equals the integral of
`p ↦ (𝓕(k)(p)).re · ‖𝓕(ψ)(p)‖²`.

This is the identity `∫ re = re ∫` (`integral_re`) together with the pointwise
computation that the real part of `z * (r : ℂ)` is `z.re * r`. -/
theorem integral_fourier_re_of_integrable {k ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hJ : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p *
        ((‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ))) :
    (∫ p : EuclideanSpace ℝ (Fin 3),
        FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p *
          ((‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ)).re
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p).re *
            ‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2 := by
  -- `(·).re` for `ℂ` is definitionally `RCLike.re`, so state the goal in that form
  -- to match `integral_re`.
  change RCLike.re (∫ p : EuclideanSpace ℝ (Fin 3),
        FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p *
          ((‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p).re *
            ‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2
  rw [← integral_re hJ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  -- pointwise: `re (z * (r : ℂ)) = z.re * r`
  show Complex.re (FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p *
          ((‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ))
      = (FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p).re *
            ‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end Work.OneBodyKin
