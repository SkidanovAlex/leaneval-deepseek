import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.Zeta

/-- Elementary bound on the distinct-prime log-weight of a natural `q ≠ 0`:
`Σ_{p | q} (log p)/p ≤ (log q)/2`.  Proof: for each prime `p | q`, `p ≥ 2`
gives `(log p)/p ≤ (log p)/2`, and `Σ_{p|q} log p = log(∏_{p|q} p) ≤ log q`
since `∏_{p|q} p` divides (hence is ≤) `q`.  Multiplies the removed-factor
estimate `removedFactors_ratio_error` (error `exp(4‖z‖Σ_{p|q}(log p)/p) − 1`)
in the uniform pole asymptotic of the modified zeta at
`1 + (1+iξ)/log x` (Polymath8a (41)). -/
theorem primeFactors_log_over_prime_sum_le (q : ℕ) (hq : q ≠ 0) :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (q : ℝ) / 2 := by
  -- For every prime p | q we have p ≥ 2, hence (log p)/p ≤ (log p)/2.
  have hstep1 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (2 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hp2n : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by norm_num)
      (by exact_mod_cast hp2n)
  -- ∑ (log p)/2 = (∑ log p)/2
  have hstep2 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (2 : ℝ)) =
      (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) / (2 : ℝ) := by
    rw [Finset.sum_div]
  -- ∑ log p = log(∏ p)
  have hstep3 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) =
      Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
    rw [← Real.log_prod]
    intro p hp
    have hp2n : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
    exact_mod_cast (ne_of_gt (by omega : 0 < p))
  -- ∏_{p|q} p divides q, so (as naturals) it is ≤ q
  have hprod_dvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
  have hprod_le_q_nat : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hprod_dvd
  have hprod_pos : (0 : ℝ) < ∏ p ∈ q.primeFactors, (p : ℝ) := by
    refine Finset.prod_pos ?_
    intro p hp
    have hp2n : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
    exact_mod_cast (by omega : 0 < p)
  have hprod_le_q : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod_le_q_nat
  -- log is monotone, and division by 2 preserves order
  have hstep4 : Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) / (2 : ℝ) ≤
      Real.log (q : ℝ) / (2 : ℝ) := by
    exact div_le_div_of_nonneg_right (Real.log_le_log hprod_pos hprod_le_q) (by norm_num)
  calc
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (2 : ℝ) := hstep1
    _ = (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) / (2 : ℝ) := hstep2
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) / (2 : ℝ) := by rw [hstep3]
    _ ≤ Real.log (q : ℝ) / (2 : ℝ) := hstep4

end Commons.NumberTheory.Zeta