import Submission.Work.FIArea5.S16.holoGaussDefs
import Submission.Work.FIArea5.S16.holoGauss_leibniz
import Submission.Work.FIArea5.S16.holoGauss_iteratedDeriv
import Submission.Work.FIArea5.S16.holoGauss_coeff

/-!
# The two-dimensional holomorphic Gaussian

The generating identity behind the "polynomial × Gaussian" Fourier analysis used in
Friedlander–Iwaniec's theorem on primes of the form `x² + y⁴`: the `m`-fold binomial sum of
one-dimensional Fourier transforms of `x^k e^{-π u x²}` collapses to the `m`-th power of the
holomorphic Gaussian phase `a + i b`.
-/

namespace Work.FIArea5.S16

open Complex Real MeasureTheory
open scoped FourierTransform

theorem holoGaussian2d (m : ℕ) {u : ℝ} (hu : 0 < u) (a b : ℝ) :
    (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
        (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
            Complex.exp (-Real.pi * u * (x : ℂ) ^ 2)) a) *
        (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
            Complex.exp (-Real.pi * u * (y : ℂ) ^ 2)) b))
      = (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ * ((a : ℂ) + Complex.I * (b : ℂ)) ^ m *
          Complex.exp (-Real.pi * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) / (u : ℂ)) := by
  have hcd : ContDiff ℂ (⊤ : ℕ∞) (gaussW u) := gaussW_contDiff u
  have hsum : (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
        (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
            Complex.exp (-Real.pi * u * (x : ℂ) ^ 2)) a) *
        (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
            Complex.exp (-Real.pi * u * (y : ℂ) ^ 2)) b))
      = (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
        ((Complex.I / (2 * Real.pi)) ^ (m - l) * iteratedDeriv (m - l) (gaussW u) (a : ℂ)) *
        ((Complex.I / (2 * Real.pi)) ^ l * iteratedDeriv l (gaussW u) (b : ℂ))) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [fourier_gaussian_poly_u hu (m - l) a, fourier_gaussian_poly_u hu l b]
  rw [hsum]
  trans (Complex.I / (2 * Real.pi)) ^ m *
      (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
        iteratedDeriv (m - l) (gaussW u) (a : ℂ) * iteratedDeriv l (gaussW u) (b : ℂ))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hp : (Complex.I / (2 * Real.pi)) ^ (m - l) * (Complex.I / (2 * Real.pi)) ^ l
        = (Complex.I / (2 * Real.pi)) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hl']
    rw [← hp]
    ring
  · rw [← holoGauss_leibniz hcd m (a : ℂ) (b : ℂ)]
    rw [holoGauss_iteratedDeriv hu m (a : ℂ) (b : ℂ)]
    rw [inv_sq_cpow_half]
    have hexp : -(Real.pi : ℂ) / (u : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2)
        = -Real.pi * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) / (u : ℂ) := by
      rw [div_mul_eq_mul_div]
    rw [hexp]
    rw [show (Complex.I / (2 * Real.pi)) ^ m * (1 / (u : ℂ) *
        Complex.exp (-Real.pi * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) / (u : ℂ)) *
        (-(2 * (Real.pi : ℂ) / (u : ℂ) * ((a : ℂ) + Complex.I * (b : ℂ)))) ^ m)
        = ((Complex.I / (2 * Real.pi)) ^ m * (1 / (u : ℂ)) *
        (-(2 * (Real.pi : ℂ) / (u : ℂ) * ((a : ℂ) + Complex.I * (b : ℂ)))) ^ m) *
        Complex.exp (-Real.pi * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) / (u : ℂ)) from by ring]
    rw [holoGauss_coeff hu m ((a : ℂ) + Complex.I * (b : ℂ))]

end Work.FIArea5.S16
