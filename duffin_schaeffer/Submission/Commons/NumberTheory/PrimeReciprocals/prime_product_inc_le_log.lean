import Mathlib
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log

namespace Commons.NumberTheory.PrimeReciprocals

open scoped BigOperators

/-- Euler product estimate: `∏_{p prime, p ≤ N} (1 + 1/p) = O(log N)`.

Follows from `Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log` (a sum bound
over the same primes) via `1 + x ≤ exp x` and `exp (log y) = y`. -/
theorem prime_product_inc_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      (∏ p ∈ Nat.primesBelow (N + 1), (1 + (1 : ℝ) / (p : ℝ))) ≤ C * Real.log (N : ℝ) := by
  rcases prime_recip_sum_le_log_log with ⟨A, hA0, hA⟩
  let C : ℝ := Real.exp A
  refine ⟨C, ?_, ?_⟩
  · exact le_of_lt (Real.exp_pos A)
  · intro N hN
    have hlogNpos : 0 < Real.log (N : ℝ) := by
      have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlog3 : 0 < Real.log (3 : ℝ) := by
        have h := Real.log_three_gt_d9
        norm_num at h
        linarith
      have hlog : Real.log (3 : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 3) hN3
      linarith
    calc
      (∏ p ∈ Nat.primesBelow (N + 1), (1 + (1 : ℝ) / (p : ℝ)))
          ≤ (∏ p ∈ Nat.primesBelow (N + 1), Real.exp ((1 : ℝ) / (p : ℝ))) := by
            refine Finset.prod_le_prod₀ ?_ ?_
            · intro p hp
              have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
              have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
              positivity
            · intro p hp
              have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
              have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
              simpa [add_comm] using (Real.add_one_le_exp ((1 : ℝ) / (p : ℝ)))
      _ = Real.exp (∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / (p : ℝ)) := by
            exact (Real.exp_sum (Nat.primesBelow (N + 1)) (fun p : ℕ => (1 : ℝ) / (p : ℝ))).symm
      _ ≤ Real.exp (A + Real.log (Real.log (N : ℝ))) := by
            exact Real.exp_le_exp.mpr (hA N hN)
      _ = Real.exp A * Real.log (N : ℝ) := by
            rw [Real.exp_add, Real.exp_log hlogNpos]
      _ = C * Real.log (N : ℝ) := by
            rfl

end Commons.NumberTheory.PrimeReciprocals
