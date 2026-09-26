import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Core.Gaussian

namespace Work.Gaussian

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

/-- The derivative of the Gaussian profile `r ↦ exp (c * r ^ 2)` at a real point. -/
private lemma hasDerivAt_gaussianProfile (c : ℂ) (x : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (c * (r : ℂ) ^ 2))
      (Complex.exp (c * (x : ℂ) ^ 2) * (c * (2 * (x : ℂ)))) x := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) ^ 2) ((2 : ℂ) * (x : ℂ)) x := by
    have h := (hasDerivAt_pow 2 x).ofReal_comp
    simpa using h
  have h2 : HasDerivAt (fun r : ℝ => c * (r : ℂ) ^ 2) (c * ((2 : ℂ) * (x : ℂ))) x :=
    h1.const_mul c
  simpa using h2.cexp

/-- The square of `sqrt (2 * k)`, read in `ℂ`. -/
private lemma sqrt_two_mul_sq {k₀ : ℕ} (k : Set.Ici k₀) :
    ((Real.sqrt (2 * (k:ℝ)) : ℝ) : ℂ) ^ 2 = ((2 * (k:ℝ) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]

/-- The values, Fourier values and radial derivatives of the complex Gaussian
`x ↦ exp (π i τ ‖x‖²)`, sampled at the radii `sqrt (2 * k)`.

Writing `f` for `Work.Core.gaussianSchwartz n τ hτ`:
* `coeffs f (k, 0) = exp (2 π i τ k)`;
* `coeffs f (k, 1) = (i/τ)^(n/2) · exp (-(2 π i k)/τ)`;
* `coeffs f (k, 2) = 2 π i τ √(2k) · exp (2 π i τ k)`;
* `coeffs f (k, 3) = 2 π i (i/τ)^(n/2) √(2k) · (-1/τ) · exp (-(2 π i k)/τ)`. -/
theorem coeffs_gaussian (n k₀ : ℕ) [NeZero n] {τ : ℂ} (hτ : 0 < τ.im) (k : Set.Ici k₀) :
    coeffs n k₀ (Work.Core.gaussianSchwartz n τ hτ) (k, 0)
        = Complex.exp (2 * ↑Real.pi * Complex.I * τ * ((k : ℕ) : ℂ))
      ∧ coeffs n k₀ (Work.Core.gaussianSchwartz n τ hτ) (k, 1)
        = (Complex.I / τ) ^ ((n : ℂ) / 2)
            * Complex.exp (-(2 * ↑Real.pi * Complex.I * ((k : ℕ) : ℂ)) / τ)
      ∧ coeffs n k₀ (Work.Core.gaussianSchwartz n τ hτ) (k, 2)
        = 2 * ↑Real.pi * Complex.I * τ * ↑(Real.sqrt (2 * (k : ℝ)))
            * Complex.exp (2 * ↑Real.pi * Complex.I * τ * ((k : ℕ) : ℂ))
      ∧ coeffs n k₀ (Work.Core.gaussianSchwartz n τ hτ) (k, 3)
        = 2 * ↑Real.pi * Complex.I * (Complex.I / τ) ^ ((n : ℂ) / 2)
            * ↑(Real.sqrt (2 * (k : ℝ))) * (-(1 / τ))
            * Complex.exp (-(2 * ↑Real.pi * Complex.I * ((k : ℕ) : ℂ)) / τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- value of the Gaussian
    show (Work.Core.gaussianSchwartz n τ hτ) (realIncl (Real.sqrt (2 * k))) = _
    rw [Work.Core.gaussianSchwartz_apply, Work.Core.gaussianFun_realIncl]
    congr 1
    rw [sqrt_two_mul_sq k]
    push_cast
    ring
  · -- value of the Fourier transform
    show (FourierTransform.fourierCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ)
        (Work.Core.gaussianSchwartz n τ hτ)) (realIncl (Real.sqrt (2 * k))) = _
    rw [Work.Core.fourier_gaussianSchwartz, Work.Core.gaussianFun_realIncl]
    congr 1
    rw [sqrt_two_mul_sq k]
    push_cast
    field_simp
  · -- radial derivative of the Gaussian
    show deriv ((Work.Core.gaussianSchwartz n τ hτ) ∘ realIncl) (Real.sqrt (2 * k)) = _
    have hfun : (Work.Core.gaussianSchwartz n τ hτ) ∘ realIncl
        = fun t : ℝ => Complex.exp (↑Real.pi * Complex.I * τ * (t:ℂ)^2) := by
      funext t
      simp only [Function.comp_apply]
      rw [Work.Core.gaussianSchwartz_apply, Work.Core.gaussianFun_realIncl]
    rw [hfun]
    rw [(hasDerivAt_gaussianProfile (↑Real.pi * Complex.I * τ) (Real.sqrt (2 * k))).deriv]
    rw [sqrt_two_mul_sq k]
    have hexp : Complex.exp (↑Real.pi * Complex.I * τ * ((2 * (k:ℝ) : ℝ) : ℂ))
        = Complex.exp (2 * ↑Real.pi * Complex.I * τ * ((k : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [hexp]
    ring
  · -- radial derivative of the Fourier transform
    show deriv ((FourierTransform.fourierCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ)
        (Work.Core.gaussianSchwartz n τ hτ)) ∘ realIncl) (Real.sqrt (2 * k)) = _
    have hfun : (FourierTransform.fourierCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ)
        (Work.Core.gaussianSchwartz n τ hτ)) ∘ realIncl
        = fun t : ℝ => (Complex.I/τ)^((n:ℂ)/2)
            * Complex.exp (↑Real.pi * Complex.I * (-1/τ) * (t:ℂ)^2) := by
      funext t
      simp only [Function.comp_apply]
      rw [Work.Core.fourier_gaussianSchwartz, Work.Core.gaussianFun_realIncl]
    rw [hfun]
    rw [((hasDerivAt_gaussianProfile (↑Real.pi * Complex.I * (-1/τ)) (Real.sqrt (2 * k))).const_mul
        ((Complex.I/τ)^((n:ℂ)/2))).deriv]
    rw [sqrt_two_mul_sq k]
    have hexp : Complex.exp (↑Real.pi * Complex.I * (-1/τ) * ((2 * (k:ℝ) : ℝ) : ℂ))
        = Complex.exp (-(2 * ↑Real.pi * Complex.I * ((k : ℕ) : ℂ)) / τ) := by
      congr 1; push_cast; field_simp
    rw [hexp]
    ring

end Work.Gaussian
