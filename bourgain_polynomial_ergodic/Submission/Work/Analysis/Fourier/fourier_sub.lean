import Mathlib
open MeasureTheory
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **Linearity of the function-level Fourier transform**: `𝓕(f - g) = 𝓕f - 𝓕g` for `L¹` functions
`f, g`.  (The `𝐞`-form produced by `Real.fourierIntegral_convergent_iff` is converted to the
`Complex.exp`-form produced by `Real.fourier_eq'` pointwise, once.) -/
lemma fourier_sub_of_integrable (f g : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ)) (ξ : ℝ) :
    FourierTransform.fourier (f - g) ξ
      = FourierTransform.fourier f ξ - FourierTransform.fourier g ξ := by
  rw [Real.fourier_eq', Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hint : ∀ (h : ℝ → ℂ), Integrable h (volume : Measure ℝ) →
      Integrable (fun x : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • h x) (volume : Measure ℝ) := by
    intro h hh
    have hc := (Real.fourierIntegral_convergent_iff ξ).2 hh
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    show (𝐞 (-(inner ℝ x ξ))) • h x
      = Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • h x
    rw [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply]
    congr 1
    push_cast
    ring
  have h1 := hint f hf
  have h2 := hint g hg
  have hpt : (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • (f - g) x)
      = fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • f x
          - Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • g x := by
    funext x
    simp only [Pi.sub_apply, smul_sub]
  rw [hpt, MeasureTheory.integral_sub h1 h2]

end Commons.Analysis.Fourier
