import Mathlib
import Submission.Work.Holonomy3.log_den_defs
import Submission.Work.Holonomy3.sum_log_primes_le
import Submission.Work.Holonomy3.log2_mul_log4_sqrt_le
import Submission.Work.Holonomy3.log_ppFac_eq_sum

namespace Work.Holonomy3

open Finset
open scoped BigOperators

/-- The sum of `log p` over the primes `p ≤ Nat.sqrt n` that occur as proper prime powers in
`ppFac` is at most `log 4 · sqrt n` (Chebyshev's bound, sharpened by `p ^ j ≤ n`, `j ≥ 2`, so
that every such prime is `≤ sqrt n`). -/
private lemma sum_inner_le (l n j : ℕ) (hj : 2 ≤ j) :
    (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
        Real.log (p : ℝ)) ≤ Real.log 4 * Real.sqrt n := by
  have hS : ∀ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
      p.Prime ∧ p ≤ Nat.sqrt n := by
    intro p hp
    obtain ⟨-, hpp, -, hpj⟩ := Finset.mem_filter.mp hp
    refine ⟨hpp, ?_⟩
    rw [Nat.le_sqrt]
    calc p * p = p ^ 2 := by ring
      _ ≤ p ^ j := Nat.pow_le_pow_right hpp.pos hj
      _ ≤ n := hpj
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h := Nat.sqrt_le n
    have h' : ((Nat.sqrt n * Nat.sqrt n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
        Real.log (p : ℝ)) ≤ Real.log 4 * (Nat.sqrt n : ℝ) := sum_log_primes_le hS
    _ ≤ Real.log 4 * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hs (Real.log_nonneg (by norm_num))

/-- The proper prime powers below `n` contribute only `O(√n·log n)` to the `lcm` of the integers
below `n`.  Chebyshev's bound `θ(x) ≤ log 4 · x` of Mathlib suffices; no PNT-style input is
needed. -/
theorem log_ppFac_bound (l n : ℕ) :
    Real.log ((Work.Holonomy3.ppFac l n : ℕ) : ℝ)
      ≤ 4 * Real.sqrt (n + 1) * (1 + Real.log (n + 1)) := by
  have hinner : ∀ j ∈ Finset.Icc 2 (Nat.log 2 n),
      (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
        Real.log (p : ℝ)) ≤ Real.log 4 * Real.sqrt n :=
    fun j hj => sum_inner_le l n j (Finset.mem_Icc.mp hj).1
  have hsum : (∑ j ∈ Finset.Icc 2 (Nat.log 2 n),
        ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
          Real.log (p : ℝ))
      ≤ (Nat.log 2 n : ℝ) * (Real.log 4 * Real.sqrt n) := by
    calc (∑ j ∈ Finset.Icc 2 (Nat.log 2 n),
          ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
            Real.log (p : ℝ))
        ≤ ∑ j ∈ Finset.Icc 2 (Nat.log 2 n), (Real.log 4 * Real.sqrt n) :=
          Finset.sum_le_sum hinner
      _ = ((Finset.Icc 2 (Nat.log 2 n)).card : ℝ) * (Real.log 4 * Real.sqrt n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.log 2 n : ℝ) * (Real.log 4 * Real.sqrt n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hc : (Finset.Icc 2 (Nat.log 2 n)).card ≤ Nat.log 2 n := by
            rw [Nat.card_Icc]; omega
          exact_mod_cast hc
  calc Real.log ((Work.Holonomy3.ppFac l n : ℕ) : ℝ)
      = ∑ j ∈ Finset.Icc 2 (Nat.log 2 n),
          ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n),
            Real.log (p : ℝ) := log_ppFac_eq_sum l n
    _ ≤ (Nat.log 2 n : ℝ) * (Real.log 4 * Real.sqrt n) := hsum
    _ ≤ 4 * Real.sqrt (n + 1) * (1 + Real.log (n + 1)) := log2_mul_log4_sqrt_le n

end Work.Holonomy3
