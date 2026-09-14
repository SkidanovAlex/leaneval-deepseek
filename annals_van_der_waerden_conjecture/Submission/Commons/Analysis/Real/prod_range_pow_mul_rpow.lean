import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.BigOperators

namespace Commons.Analysis.Real

open Finset

/-- Auxiliary summation identity: for every `m`,
`(∑ i ∈ range m, (m + 1 - i)) + 1 = ∑ k ∈ range (m + 2), k`.
Equivalently, `(m+1) + m + ⋯ + 2 + 1 = 1 + 2 + ⋯ + (m+1)`. -/
lemma sum_range_sub_pred_add_one (m : ℕ) :
    (∑ i ∈ Finset.range m, (m + 1 - i)) + 1 = ∑ k ∈ Finset.range (m + 2), k := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hstep : (∑ i ∈ Finset.range (m + 1), (m + 1 + 1 - i))
          = (∑ i ∈ Finset.range m, (m + 1 - i)) + (m + 2) := by
        rw [Finset.sum_range_succ' (fun i => (m + 1) + 1 - i) m]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        omega
      rw [hstep, add_right_comm, ih]
      rw [← Finset.sum_range_succ (fun k => k) (m + 2)]

/-- Summation identity for the exponent appearing in `prod_range_pow_mul_rpow`:
for `1 ≤ n`, `∑ i ∈ range (n - 1), (n - i) = n * (n + 1) / 2 - 1`. -/
lemma sum_range_sub_pred (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n - 1), (n - i)) = n * (n + 1) / 2 - 1 := by
  have h := sum_range_sub_pred_add_one (n - 1)
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hn2 : (n - 1) + 2 = n + 1 := by omega
  rw [hn1, hn2] at h
  have h2 : ∑ k ∈ Finset.range (n + 1), k = n * (n + 1) / 2 := by
    rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]
  rw [h2] at h
  exact Nat.eq_sub_of_add_eq h

theorem prod_range_pow_mul_rpow (n : ℕ) (a x : ℝ) (hn : 1 ≤ n) :
    (∏ i ∈ Finset.range (n - 1), a ^ n * x ^ (n - i))
      = a ^ (n * (n - 1)) * x ^ (n * (n + 1) / 2 - 1) := by
  rw [Finset.prod_mul_distrib]
  have ha : (∏ i ∈ Finset.range (n - 1), a ^ n) = a ^ (n * (n - 1)) := by
    rw [Finset.prod_const, Finset.card_range, ← pow_mul]
  have hx : (∏ i ∈ Finset.range (n - 1), x ^ (n - i)) = x ^ (n * (n + 1) / 2 - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_range_sub_pred n hn]
  rw [ha, hx]

end Commons.Analysis.Real