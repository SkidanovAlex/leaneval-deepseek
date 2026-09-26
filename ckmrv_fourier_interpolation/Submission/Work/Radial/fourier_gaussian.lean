import Mathlib
import Submission.Work.Core.Basic

/-!
# The Fourier transform of the complex Gaussian on `R^n`

For `τ : ℂ` with `0 < τ.im` the function

`x ↦ exp (π i τ ‖x‖ ^ 2)`

is a Schwartz function on `EuclideanSpace ℝ (Fin n)` (see
`Work.Radial.gaussian_schwartz`), and its Fourier transform is

`w ↦ (i / τ) ^ (n / 2) · exp (-π i ‖w‖ ^ 2 / τ)`,

i.e. the Gaussian with parameter `-1 / τ` times the classical factor
`(i / τ) ^ (n / 2)`.

The proof is the `n`-dimensional generalisation of Mathlib's
`fourier_gaussian_innerProductSpace` (valid in any finite-dimensional real inner
product space), specialised to `b = -π i τ`, together with the elementary
identifications `π / (-π i τ) = i / τ` and
`-π ^ 2 ‖w‖ ^ 2 / (-π i τ) = π i (-1 / τ) ‖w‖ ^ 2`.
-/

namespace Work.Radial

open scoped FourierTransform SchwartzMap
open LeanEval.Analysis.CKMRVInterpolation

theorem fourier_gaussian (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im)
    (G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hG : ∀ x, G x = Work.Core.gaussianFun n τ x)
    (w : EuclideanSpace ℝ (Fin n)) :
    (FourierTransform.fourierCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) G) w
      = (Complex.I / τ) ^ ((n : ℂ) / 2) * Work.Core.gaussianFun n (-1 / τ) w := by
  have hπ : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  set b : ℂ := -(↑Real.pi * Complex.I * τ) with hbdef
  have hb : 0 < b.re := by
    rw [hbdef]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_im, mul_zero]
    nlinarith [Real.pi_pos, hτ]
  have key := fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin n)) hb w
  rw [FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe]
  rw [show (⇑G : EuclideanSpace ℝ (Fin n) → ℂ) = fun v => Complex.exp (-b * ↑‖v‖ ^ 2) from by
    funext v
    rw [hG v, Work.Core.gaussianFun]
    congr 1
    rw [hbdef]; push_cast; ring]
  rw [key, finrank_euclideanSpace_fin]
  have hbτ : (↑Real.pi : ℂ) / b = Complex.I / τ := by
    rw [hbdef]
    field_simp
    rw [pow_two, Complex.I_mul_I]
  rw [hbτ]
  congr 1
  rw [Work.Core.gaussianFun]
  congr 1
  rw [hbdef]
  push_cast
  field_simp
  ring_nf
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
  rw [hI]
  ring

end Work.Radial
