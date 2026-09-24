import Mathlib
import Submission.Commons.NumberTheory.Sieve.prod_one_add_inv_prime_le_log_of_two_le

namespace Work.ChenPlan.H1

open scoped BigOperators

/-- Mertens-type upper bound for the Euler factor `1 + 9/p`: `∏_{p ≤ N} (1 + 9/p) ≤ C (log N)^9`.

A proof can use `Commons.NumberTheory.Sieve.prod_one_add_inv_prime_le_log_of_two_le`
(`∃ C > 0, ∀ z ≥ 2, ∏_{p ∈ Nat.primesBelow z} (1 + 1/p) ≤ C log z`) together with the
binomial bound `1 + 9/p ≤ (1 + 1/p)^9` (or
`Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog`). -/
theorem prod_primes_one_add_nine_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / (p : ℝ))) ≤ C * (Real.log (N : ℝ)) ^ 9 := by
  -- Euler–Mertens: `∏_{p < z} (1 + 1/p) ≤ C log z`.
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.Sieve.prod_one_add_inv_prime_le_log_of_two_le
  -- Bernoulli: `1 + 9/p ≤ (1 + 1/p)^9`, so raising the Mertens product to the ninth
  -- power dominates our product.  The loss `log (N+1) ≤ 2 log N` costs `2^9 = 512`.
  refine ⟨C ^ 9 * 512, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℕ) < N := by omega
  have hNR2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNRpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hprod1 :
      (∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ))) ≤ C * Real.log ((N : ℝ) + 1) := by
    have h := hC (N + 1) (by omega)
    simpa using h
  -- Bernoulli termwise bound `1 + 9/p ≤ (1 + 1/p)^9` for every prime `p`.
  have hstep1 : (∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / (p : ℝ)))
      ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)) ^ 9 := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      positivity
    · intro p hp
      have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hx : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      have h := one_add_mul_le_pow (a := 1 / (p : ℝ)) (by linarith) 9
      simpa [div_eq_mul_inv] using h
  -- `log (N+1) ≤ 2 log N` for `N ≥ 2`.
  have hlogcmp : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
    have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) := by
      refine Real.log_le_log (by linarith) ?_
      linarith
    have h2 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hNRpos)
    have h3 : Real.log 2 ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) hNR2
    linarith
  have hprod1pos : 0 ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
      exact_mod_cast (by omega : 0 < p)
    positivity
  have hlogN1pos : 0 < Real.log ((N : ℝ) + 1) := by
    refine Real.log_pos ?_
    linarith
  calc (∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / (p : ℝ)))
      ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ)) ^ 9 := hstep1
    _ = (∏ p ∈ Nat.primesBelow (N + 1), (1 + 1 / (p : ℝ))) ^ 9 :=
        Finset.prod_pow (Nat.primesBelow (N + 1)) 9 (fun p => 1 + 1 / (p : ℝ))
    _ ≤ (C * Real.log ((N : ℝ) + 1)) ^ 9 := pow_le_pow_left₀ hprod1pos hprod1 9
    _ ≤ (C * (2 * Real.log (N : ℝ))) ^ 9 := by
        refine pow_le_pow_left₀ ?_ ?_ 9
        · positivity
        · exact mul_le_mul_of_nonneg_left hlogcmp hCpos.le
    _ = C ^ 9 * 512 * (Real.log (N : ℝ)) ^ 9 := by ring

end Work.ChenPlan.H1
