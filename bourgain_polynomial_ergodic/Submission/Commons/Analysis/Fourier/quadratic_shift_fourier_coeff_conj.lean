import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Fourier

open Finset MeasureTheory
open scoped BigOperators

/-- The period integral of an integer-frequency exponential over `[0,1]`:
`∫₀¹ e^{2πi n θ} dθ` is `1` for `n = 0` and `0` otherwise. -/
lemma integral_exp_two_pi_int (n : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * θ)))
      = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn]
    set c : ℂ := 2 * Real.pi * Complex.I * (n : ℂ) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hn)
    have hfun : (fun θ : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * θ)))
        = fun θ : ℝ => Complex.exp (c * (θ : ℂ)) := by
      funext θ
      rw [hc]
      congr 1
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex (a := (0:ℝ)) (b := (1:ℝ)) hc0]
    have h1 : Complex.exp (c * ((1:ℝ):ℂ)) = 1 := by
      have hceq : c * ((1:ℝ):ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hc]; push_cast; ring
      rw [hceq, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (c * ((0:ℝ):ℂ)) = 1 := by simp
    rw [h1, h0]
    simp

/-- **Fourier multiplier identity for the forward square averages on `ℤ` (corrected sign).**

For a finitely supported `g : ℤ → ℂ`, the average `(1/N) ∑_{i<N} g (· + i²)` has `k`-th
Fourier coefficient `(1/N) ∑_{i<N} g (k + i²)`, and its Fourier multiplier is the
*conjugate* square kernel `(1/N) ∑_{i<N} e(-2πi i²θ)`:
`(1/N) ∑_{i<N} g (k + i²) = ∫_0^1 K̄_N(θ) ĝ(θ) e^{-2πi k θ} dθ`
where `ĝ(θ) = ∑_m g(m) e(2πi m θ)`.
Useful intermediate facts: `∑_m g(m) e(2πi m θ)` may be taken over any finite `s` containing
the support of `g`, and `∫_0^1 e(2πi n θ) dθ` is `1` for `n = 0` and `0` otherwise.
(The variant with the un-conjugated kernel `e(+2πi i²θ)` computes instead the *backward*
average `(1/N) ∑_{i<N} g (k - i²)`, so the statement with `g (k + i²)` and that kernel is
false.) -/
theorem quadratic_shift_fourier_coeff_conj (g : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → g n = 0) (N : ℕ) (k : ℤ) :
    (∫ θ in (0:ℝ)..1,
        ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ 2) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, g (k + (i : ℤ) ^ 2) := by
  -- Pointwise rewrite of the integrand as a double sum of single exponentials.
  have hpt : ∀ θ : ℝ,
      ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ 2) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ)))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ 2 - k : ℤ) : ℝ)) * θ)) := by
    intro θ
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro m _
    have hexp : Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ 2 - k : ℤ) : ℝ)) * θ))
        = Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ 2) * θ)))
          * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  -- Compute the integral of the double sum.
  have hint : ∀ i : ℕ,
      (∫ θ in (0:ℝ)..1, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ 2 - k : ℤ) : ℝ)) * θ)))
        = ∑ m ∈ s, g m * (if (m - (i : ℤ) ^ 2 - k) = 0 then 1 else 0) := by
    intro i
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m _
      rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_int]
    · intro m _
      exact Continuous.intervalIntegrable (by fun_prop) 0 1
  have hstep : ∀ i : ℕ,
      (∑ m ∈ s, g m * (if (m - (i : ℤ) ^ 2 - k) = 0 then 1 else 0))
        = g (k + (i : ℤ) ^ 2) := by
    intro i
    have hiff : ∀ m : ℤ, (m - (i : ℤ) ^ 2 - k = 0) ↔ (m = k + (i : ℤ) ^ 2) := by
      intro m; constructor <;> intro h <;> omega
    have hstep' : ∀ m : ℤ, g m * (if m = k + (i : ℤ) ^ 2 then 1 else 0)
        = if m = k + (i : ℤ) ^ 2 then g m else 0 := by
      intro m; by_cases h : m = k + (i : ℤ) ^ 2 <;> simp [h]
    simp only [hiff, hstep', Finset.sum_ite_eq']
    by_cases hb : (k + (i : ℤ) ^ 2) ∈ s
    · simp [hb]
    · simp [hb, hs (k + (i : ℤ) ^ 2) hb]
  rw [show (∫ θ in (0:ℝ)..1,
        ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ 2) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))))
      = ∫ θ in (0:ℝ)..1, (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ 2 - k : ℤ) : ℝ)) * θ))
      from intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum
        (f := fun (i : ℕ) (θ : ℝ) => ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ 2 - k : ℤ) : ℝ)) * θ)))]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hint i, hstep i]
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) 0 1

end Commons.Analysis.Fourier