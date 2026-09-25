import Mathlib
import Submission.Commons.Analysis.Fourier.quadratic_shift_fourier_coeff_conj

namespace Work.BourgainPlan.Maximal

open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

/-- **Fourier identity for the polynomial shifts.**  For a finitely supported `g : ℤ → ℂ`, the
polynomial average `N⁻¹ ∑_{i<N} g (k + P i)` is the Fourier coefficient of (the conjugate of) the
polynomial Weyl kernel times the Fourier series of `g`:

`∫_0^1 (N⁻¹ ∑_{i<N} e(-2πi (P i) θ)) · (∑_m g m e(2πi m θ)) · e(-2πi k θ) dθ = N⁻¹ ∑_{i<N} g (k + P i)`.

Here `P i` is the honest integer value `P.eval i` (no `toNat`, so the identity holds for every
integer polynomial and every `k : ℤ`; under `NonnegOnNat` it coincides with the `toNat` form used by
`discAvgZ`, since `P.eval i ≥ 0` there).  This is the general-polynomial analogue of
`Commons.Analysis.ExponentialSums.pow_shift_fourier_coeff_conj` (replace `i^d` by `P i` throughout);
its proof is the same: expand the product, exchange the sums, and use
`Commons.Analysis.Fourier.integral_exp_two_pi_int`. -/
theorem shift_fourier_coeff_conj (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → g n = 0) (N : ℕ) (k : ℤ) :
    (∫ θ in (0 : ℝ)..1,
        ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ) : ℝ)) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, g (k + P.eval (i : ℤ)) := by
  have hpt : ∀ θ : ℝ,
      ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ) : ℝ)) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ)))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I *
            ((((m - P.eval (i : ℤ) - k : ℤ) : ℝ)) * θ)) := by
    intro θ
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro m _
    have hexp : Complex.exp (2 * Real.pi * Complex.I *
          ((((m - P.eval (i : ℤ) - k : ℤ) : ℝ)) * θ))
        = Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ) : ℝ)) * θ)))
          * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  have hint : ∀ i : ℕ,
      (∫ θ in (0:ℝ)..1, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I *
            ((((m - P.eval (i : ℤ) - k : ℤ) : ℝ)) * θ)))
        = ∑ m ∈ s, g m * (if (m - P.eval (i : ℤ) - k) = 0 then 1 else 0) := by
    intro i
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m _
      rw [intervalIntegral.integral_const_mul, Commons.Analysis.Fourier.integral_exp_two_pi_int]
    · intro m _
      exact Continuous.intervalIntegrable (by fun_prop) 0 1
  have hstep : ∀ i : ℕ,
      (∑ m ∈ s, g m * (if (m - P.eval (i : ℤ) - k) = 0 then 1 else 0))
        = g (k + P.eval (i : ℤ)) := by
    intro i
    have hiff : ∀ m : ℤ, (m - P.eval (i : ℤ) - k = 0) ↔ (m = k + P.eval (i : ℤ)) := by
      intro m; constructor <;> intro h <;> omega
    have hstep' : ∀ m : ℤ, g m * (if m = k + P.eval (i : ℤ) then 1 else 0)
        = if m = k + P.eval (i : ℤ) then g m else 0 := by
      intro m; by_cases h : m = k + P.eval (i : ℤ) <;> simp [h]
    simp only [hiff, hstep', Finset.sum_ite_eq']
    by_cases hb : (k + P.eval (i : ℤ)) ∈ s
    · simp [hb]
    · simp [hb, hs (k + P.eval (i : ℤ)) hb]
  trans (∫ θ in (0:ℝ)..1, (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ s,
      g m * Complex.exp (2 * Real.pi * Complex.I *
        ((((m - P.eval (i : ℤ) - k : ℤ) : ℝ)) * θ)))
  · exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
  · rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum
          (f := fun (i : ℕ) (θ : ℝ) => ∑ m ∈ s,
            g m * Complex.exp (2 * Real.pi * Complex.I *
              ((((m - P.eval (i : ℤ) - k : ℤ) : ℝ)) * θ)))]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hint i, hstep i]
    · intro i _
      exact Continuous.intervalIntegrable (by fun_prop) 0 1

end Work.BourgainPlan.Maximal
