import Mathlib
import Submission.Work.FIArea5.S16.fourier_gaussian_poly

/-!
# Holomorphic Gaussian: shared definitions

This file collects the frequency-domain Gaussian used by
`Work.FIArea5.S16.fourier2d_holoGaussian`, together with the direct corollary of
`Work.FIArea5.S16.fourier_gaussian_poly` that identifies the Fourier transform of
`x ↦ x ^ k * exp (-π u x²)` with the `k`-th derivative of that Gaussian.
-/

namespace Work.FIArea5.S16

open Complex Real MeasureTheory
open scoped FourierTransform

/-- The (frequency side of the) Gaussian `w ↦ u^{-1/2} e^{-π w²/u}`, as a function on `ℂ`. -/
noncomputable def gaussW (u : ℝ) : ℂ → ℂ :=
  fun w => (1 / (u : ℂ) ^ (1 / 2 : ℂ)) * Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * w ^ 2)

/-- **Fourier transform of a polynomially weighted Gaussian** (real, non-normalised version
of `fourier_gaussian_poly`, with vanishing linear term).

For `0 < u`, `𝓕 (x ↦ x^k e^{-π u x²})` is `(i/2π)^k` times the `k`-th derivative of the
frequency-side Gaussian `gaussW u`. -/
theorem fourier_gaussian_poly_u {u : ℝ} (hu : 0 < u) (k : ℕ) (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ k) *
        Complex.exp (-Real.pi * u * (x : ℂ) ^ 2)) ξ
      = (Complex.I / (2 * Real.pi)) ^ k *
        iteratedDeriv k (gaussW u) (ξ : ℂ) := by
  have hu' : 0 < ((u : ℂ)).re := by simpa using hu
  have h := fourier_gaussian_poly k hu' (0 : ℂ) ξ
  have hfun : (fun x : ℝ => (x : ℂ) ^ k * Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))
      = (fun x : ℝ => (x : ℂ) ^ k *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (x : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * (0 : ℂ) * (x : ℂ))) := by
    funext x; congr 2 <;> ring
  rw [hfun, h]
  congr 1
  exact Filter.EventuallyEq.iteratedDeriv_eq k
    (by filter_upwards with w; simp only [gaussW, mul_zero, add_zero])

lemma gaussW_contDiff (u : ℝ) : ContDiff ℂ (⊤ : ℕ∞) (gaussW u) := by
  unfold gaussW; fun_prop

/-- `(u^{-1/2})² = u^{-1}` for the principal square root `u^(1/2)`; valid for every complex `u`. -/
lemma inv_sq_cpow_half (u : ℂ) : (1 / u ^ (1 / 2 : ℂ)) ^ 2 = 1 / u := by
  rw [one_div, inv_pow, show (1 / 2 : ℂ) = (((2 : ℕ) : ℂ))⁻¹ by norm_num,
    Complex.cpow_nat_inv_pow u (by norm_num), one_div]

end Work.FIArea5.S16
