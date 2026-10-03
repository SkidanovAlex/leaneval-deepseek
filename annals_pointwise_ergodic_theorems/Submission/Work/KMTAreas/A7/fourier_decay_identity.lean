import Mathlib

/-!
# Fourier decay identity for the second derivative

For a `C²` function `f : ℝ → ℂ` whose first two derivatives are integrable, and for every
frequency `ξ : ℝ`,

  `(2πξ)² · ∫ f(x) e^{-2πiξx} dx = - ∫ f''(x) e^{-2πiξx} dx`.

This is the classical formula `𝓕(f'') = -(2πξ)² 𝓕 f` (twice integration by parts), expressed in
terms of the explicit oscillatory integrals.  Rather than integrating by parts we use Mathlib's
`Real.fourier_iteratedDeriv`, which identifies the Fourier transform of `iteratedDeriv n f` with
`(2πiξ)^n` times the Fourier transform of `f`; the result is then the purely algebraic identity
`(2πiξ)² = -(2πξ)²`.
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.KMTAreas.A7

theorem fourier_decay_identity (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hint0 : MeasureTheory.Integrable f) (hint1 : MeasureTheory.Integrable (deriv f))
    (hint2 : MeasureTheory.Integrable (fun x : ℝ => iteratedDeriv 2 f x)) (ξ : ℝ) :
    ((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2 *
        (∫ x : ℝ, f x * Complex.exp (2 * Real.pi * Complex.I * (-(ξ * x)))) =
      - (∫ x : ℝ, iteratedDeriv 2 f x * Complex.exp (2 * Real.pi * Complex.I * (-(ξ * x)))) := by
  -- Integrability of the first two iterated derivatives, in the form needed by
  -- `Real.fourier_iteratedDeriv`.
  have hInt : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n f) := by
    intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    interval_cases n
    · rw [iteratedDeriv_zero]; exact hint0
    · rw [iteratedDeriv_one]; exact hint1
    · exact hint2
  have hF2 := Real.fourier_iteratedDeriv (N := (2 : ℕ∞)) (n := 2) hf hInt (by norm_num)
  -- Identify the two oscillatory integrals with Fourier transforms.
  have hleft : (∫ x : ℝ, f x * Complex.exp (2 * Real.pi * Complex.I * (-(ξ * x)))) = 𝓕 f ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    rw [smul_eq_mul, mul_comm (f v)]
    congr 1
    congr 1
    push_cast
    ring
  have hright :
      (∫ x : ℝ, iteratedDeriv 2 f x * Complex.exp (2 * Real.pi * Complex.I * (-(ξ * x)))) =
        𝓕 (iteratedDeriv 2 f) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    rw [smul_eq_mul, mul_comm (iteratedDeriv 2 f v)]
    congr 1
    congr 1
    push_cast
    ring
  rw [hleft, hright, congr_fun hF2 ξ, smul_eq_mul]
  -- It remains to check `(2πiξ)² = -(2πξ)²` and commute the scalar out of the factor.
  have hI : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2 = - ((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2
          = (2 * (Real.pi : ℂ) * (ξ : ℂ)) ^ 2 * Complex.I ^ 2 by ring]
    rw [Complex.I_sq, ← Complex.ofReal_pow]
    push_cast
    ring
  rw [hI]
  ring

end Work.KMTAreas.A7
