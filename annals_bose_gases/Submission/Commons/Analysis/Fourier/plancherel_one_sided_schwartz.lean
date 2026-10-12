import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap

namespace Commons.Analysis.Fourier

/-- **One-sided Plancherel / multiplication formula.**

If `f` is integrable and `g` is a Schwartz function on a finite-dimensional real inner product
space `V`, then
`∫ x, f x * g x = ∫ p, 𝓕 f p * 𝓕 g (-p)`.

This is the (conjugate-free) Plancherel/multiplication identity in the "one-sided" regime where
only one of the two functions is a priori smooth. The proof is the self-adjointness of the Fourier
transform for `L¹` functions (`VectorFourier.integral_bilin_fourierIntegral_eq_flip`) applied to `f`
and to the inverse Fourier transform `𝓕⁻ g` of the Schwartz function `g` — which is again a
Schwartz function, hence integrable — combined with Fourier inversion `𝓕 (𝓕⁻ g) = g` and the
pointwise identity `𝓕⁻ g = 𝓕 g (-·)`.

With Mathlib's convention `𝓕 f p = ∫ x, e^{-2πi⟪x,p⟫} f x` this is equivalently
`∫ f g = ∫ 𝓕 f · 𝓕⁻ g`. -/
theorem plancherel_one_sided_schwartz_general {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hf : MeasureTheory.Integrable f) (g : SchwartzMap V ℂ) :
    (∫ x, f x * g x) = ∫ p, FourierTransform.fourier f p *
      FourierTransform.fourier (g : V → ℂ) (-p) := by
  -- The inverse Fourier transform of `g`, as an ordinary function; being a Schwartz function
  -- it is integrable.
  let hinv : V → ℂ := fun x => (𝓕⁻ g : 𝓢(V, ℂ)) x
  -- Fourier inversion: `𝓕 hinv = g`.
  have hFourier : 𝓕 hinv = fun x => (g : V → ℂ) x := by
    rw [← SchwartzMap.fourier_coe (𝓕⁻ g), FourierTransform.fourier_fourierInv_eq]
  -- `hinv = 𝓕⁻ g = 𝓕 g (-·)` pointwise.
  have hInv : ∀ p, hinv p = FourierTransform.fourier (g : V → ℂ) (-p) := by
    intro p
    change (𝓕⁻ g : 𝓢(V, ℂ)) p = _
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  have hint : MeasureTheory.Integrable hinv := (𝓕⁻ g).integrable
  -- Self-adjointness of the Fourier transform for `L¹` functions.
  have key := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (e := 𝐞) (μ := volume) (ν := volume) (L := innerₗ V)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar continuous_inner hf hint
  calc (∫ x, f x * g x)
      = ∫ x, f x * (VectorFourier.fourierIntegral 𝐞 volume (innerₗ V).flip hinv x) := by
          apply integral_congr_ae; filter_upwards with x
          congr 1
          rw [show (innerₗ V).flip = innerₗ V from flip_innerₗ V]
          change (g : V → ℂ) x = (𝓕 hinv) x
          rw [hFourier]
    _ = ∫ ξ, 𝓕 f ξ * hinv ξ := key.symm
    _ = ∫ p, FourierTransform.fourier f p * FourierTransform.fourier (g : V → ℂ) (-p) := by
          apply integral_congr_ae; filter_upwards with p
          rw [hInv p]

/-- **One-sided Plancherel / multiplication formula on `ℝ³`.**

If `f` is integrable and `g` is a Schwartz function on `ℝ³`, then
`∫ x, f x * g x = ∫ p, 𝓕 f p * 𝓕 g (-p)`.

This is the Plancherel/multiplication identity in the "one-sided" regime where only one of the
two functions is known to be smooth; it is an immediate instance of
`plancherel_one_sided_schwartz_general`. -/
theorem plancherel_one_sided_schwartz {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : MeasureTheory.Integrable f) (g : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    (∫ x, f x * g x) = ∫ p, FourierTransform.fourier f p *
      FourierTransform.fourier (g : EuclideanSpace ℝ (Fin 3) → ℂ) (-p) :=
  plancherel_one_sided_schwartz_general hf g

end Commons.Analysis.Fourier