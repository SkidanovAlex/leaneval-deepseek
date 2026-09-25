import Mathlib
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionImports

namespace Work.BourgainPlan.Maximal

/--
**Convolution equals the multiplier form.**  For an integrable symbol `Θ : ℝ → ℂ` and a Schwartz
function `G`, the convolution of `G` with the inverse Fourier transform of `Θ` is the inverse
Fourier transform of the pointwise product `Θ · 𝓕G`:
`(𝓕⁻Θ * G)(x) = ∫ ξ, Θ ξ * e^{2πi x ξ} * 𝓕G(ξ) dξ`.

This is the `L¹`-multiplier identity: writing `𝓕⁻Θ` as the (distributional) multiplier with symbol
`Θ` makes `𝓕⁻Θ * G` the operator "multiply `𝓕G` by `Θ`", and the right-hand side exhibits the
multiplier action as an integral against the phase `e^{2πi x ξ}`. -/
theorem convolutionEqMultiplierSchwartz (Θ : ℝ → ℂ)
    (hΘ : MeasureTheory.Integrable Θ (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (G : SchwartzMap ℝ ℂ) :
    (fun x : ℝ => ∫ y : ℝ, FourierTransformInv.fourierInv Θ (x - y) * (G : ℝ → ℂ) y)
      = fun x : ℝ => ∫ ξ : ℝ,
        (Θ ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • FourierTransform.fourier (G : ℝ → ℂ) ξ := by
  funext x
  -- The right-hand side is `𝓕⁻(Θ · 𝓕G)` evaluated at `x`, by definition of the inverse transform.
  have h1 : (∫ ξ : ℝ, (Θ ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • FourierTransform.fourier (G : ℝ → ℂ) ξ)
      = FourierTransformInv.fourierInv
          (fun ξ => Θ ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) x := by
    rw [Real.fourierInv_eq']
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ξ
    rw [Real.inner_apply]
    simp only [smul_eq_mul]
    rw [show (↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I = 2 * Real.pi * Complex.I * (x * ξ) from by
      push_cast; ring]
    ring
  rw [h1]
  -- `𝓕⁻(Θ · 𝓕G) = G * 𝓕⁻Θ` (Fourier inversion commuted with multiplication).
  rw [Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution hΘ G.integrable x]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  ring

end Work.BourgainPlan.Maximal
