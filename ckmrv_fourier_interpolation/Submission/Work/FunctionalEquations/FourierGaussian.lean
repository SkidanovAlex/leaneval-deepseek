import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Radial.fourier_gaussian
import Submission.Work.Radial.gaussian_schwartz

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- **Fourier transform of the complex Gaussian** (paper (3.3), cf. Mathlib's
`fourier_gaussian_innerProductSpace`).  For `τ` in the upper half plane the Fourier
transform of `x ↦ exp (π i τ ‖x‖²)` is `(i/τ)^{n/2}` times the Gaussian with parameter
`-1/τ`.

This is the pointwise form of the transform: it is stated for the function
`gaussianFun n τ` itself, without first packaging it as a Schwartz function. -/
theorem FourierGaussian {n : ℕ} [NeZero n] (τ : ℂ) (hτ : 0 < τ.im) (x : E n) :
    𝓕 (Work.Core.gaussianFun n τ) x
      = slashFactor n τ * Work.Core.gaussianFun n (-1 / τ) x := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  set b : ℂ := -(↑Real.pi * Complex.I * τ) with hbdef
  have hb : 0 < b.re := by
    rw [hbdef]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_im, mul_zero]
    nlinarith [Real.pi_pos, hτ]
  have key := fourier_gaussian_innerProductSpace (V := E n) hb x
  rw [show (Work.Core.gaussianFun n τ) = fun v : E n => Complex.exp (-b * ↑‖v‖ ^ 2) from by
    funext v
    rw [Work.Core.gaussianFun]
    congr 1
    rw [hbdef]; push_cast; ring]
  rw [key]
  simp only [finrank_euclideanSpace_fin]
  have hbτ : (↑Real.pi : ℂ) / b = Complex.I / τ := by
    rw [hbdef]
    field_simp
    rw [pow_two, Complex.I_mul_I]
  rw [hbτ]
  rw [Work.Core.gaussianFun]
  have harg : -↑Real.pi ^ 2 * ↑‖x‖ ^ 2 / b
      = ↑Real.pi * Complex.I * (-1 / τ) * ↑(‖x‖ ^ 2) := by
    rw [hbdef]
    field_simp
    rw [Complex.I_sq]
    push_cast
    ring
  rw [harg]
  rfl

end Work.FunctionalEquations
