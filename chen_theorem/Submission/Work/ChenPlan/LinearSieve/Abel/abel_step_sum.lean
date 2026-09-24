import Mathlib

/-!
# Abel summation step bound for the linear sieve

This file proves `abel_step_sum`, a comparison (Abel / partial-summation) estimate used in the
linear sieve: if `P : ℕ → ℝ` is nondecreasing from `w ≤ P 0` up to `P n = Z`, if `M ≤ T` pointwise
on the values `P k` (`k ≤ n`), and if `Φ` is nonnegative and nondecreasing on `[w, Z]`, then

`∑_{i<n} (M(P i) - M(P (i+1))) Φ(P i) ≤ (T Z - M Z) Φ Z + ∑_{i<n} (T(P i) - T(P (i+1))) Φ(P i)`.

The mathematical content is the summation-by-parts identity

`C n Φ n + ∑_{i<n} (C i - C (i+1)) Φ i = C 0 Φ 0 + ∑_{i<n} C (i+1) (Φ (i+1) - Φ i)`

applied to `C k = T (P k) - M (P k) ≥ 0`.
-/

open Finset

namespace Work.ChenPlan.LinearSieve.Abel

/-- **Summation by parts (Abel transformation)** in its "reversed telescoping" form:
`C n φ n + ∑_{i<n} (C i - C (i+1)) φ i = C 0 φ 0 + ∑_{i<n} C (i+1) (φ (i+1) - φ i)`. -/
private lemma abel_telescope (C φ : ℕ → ℝ) (n : ℕ) :
    C n * φ n + ∑ i ∈ Finset.range n, (C i - C (i + 1)) * φ i
      = C 0 * φ 0 + ∑ i ∈ Finset.range n, C (i + 1) * (φ (i + 1) - φ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linear_combination ih

/-- The comparison step in the abstract form: for sequences `A ≤ B` and a nonnegative nondecreasing
weight `φ`, the `A`-weighted Abel sum is bounded by the boundary term plus the `B`-weighted Abel sum. -/
private lemma step_sum_aux {n : ℕ} (A B φ : ℕ → ℝ)
    (hAB : ∀ k, k ≤ n → A k ≤ B k) (hφ0 : 0 ≤ φ 0)
    (hφmono : ∀ i, i < n → φ i ≤ φ (i + 1)) :
    ∑ i ∈ Finset.range n, (A i - A (i + 1)) * φ i
      ≤ (B n - A n) * φ n + ∑ i ∈ Finset.range n, (B i - B (i + 1)) * φ i := by
  have hnonneg : 0 ≤ (B n - A n) * φ n
      + ∑ i ∈ Finset.range n, ((B i - B (i + 1)) - (A i - A (i + 1))) * φ i := by
    have hid : (B n - A n) * φ n
        + ∑ i ∈ Finset.range n, ((B i - B (i + 1)) - (A i - A (i + 1))) * φ i
        = (B 0 - A 0) * φ 0
          + ∑ i ∈ Finset.range n, (B (i + 1) - A (i + 1)) * (φ (i + 1) - φ i) := by
      have htel' : (B n - A n) * φ n
          + ∑ i ∈ Finset.range n, ((B i - A i) - (B (i + 1) - A (i + 1))) * φ i
          = (B 0 - A 0) * φ 0
            + ∑ i ∈ Finset.range n, (B (i + 1) - A (i + 1)) * (φ (i + 1) - φ i) :=
        abel_telescope (fun k => B k - A k) φ n
      have hsum_eq : ∑ i ∈ Finset.range n, ((B i - B (i + 1)) - (A i - A (i + 1))) * φ i
          = ∑ i ∈ Finset.range n, ((B i - A i) - (B (i + 1) - A (i + 1))) * φ i := by
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hsum_eq, htel']
    rw [hid]
    apply add_nonneg
    · exact mul_nonneg (by linarith [hAB 0 (Nat.zero_le n)]) hφ0
    · apply Finset.sum_nonneg
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      exact mul_nonneg (by linarith [hAB (i + 1) (Nat.succ_le_of_lt hi')])
        (by linarith [hφmono i hi'])
  have hsplit : ∑ i ∈ Finset.range n, ((B i - B (i + 1)) - (A i - A (i + 1))) * φ i
      = ∑ i ∈ Finset.range n, (B i - B (i + 1)) * φ i
        - ∑ i ∈ Finset.range n, (A i - A (i + 1)) * φ i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [← sub_nonneg]
  rw [hsplit] at hnonneg
  linarith

theorem abel_step_sum {n : ℕ} {P : ℕ → ℝ} (hPmono : Monotone P)
    {w Z : ℝ} (hwP0 : w ≤ P 0) (hPn : P n = Z)
    {M T : ℝ → ℝ} (hMT : ∀ k : ℕ, k ≤ n → M (P k) ≤ T (P k))
    {Φ : ℝ → ℝ} (hΦmono : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z → Φ a ≤ Φ b)
    (hΦnn : ∀ a : ℝ, w ≤ a → a ≤ Z → 0 ≤ Φ a) :
    ∑ i ∈ Finset.range n, (M (P i) - M (P (i + 1))) * Φ (P i)
      ≤ (T Z - M Z) * Φ Z
        + ∑ i ∈ Finset.range n, (T (P i) - T (P (i + 1))) * Φ (P i) := by
  rw [← hPn]
  refine step_sum_aux (fun k => M (P k)) (fun k => T (P k)) (fun k => Φ (P k))
    hMT ?_ ?_
  · exact hΦnn (P 0) hwP0 (le_trans (hPmono (Nat.zero_le n)) (le_of_eq hPn))
  · intro i hi
    exact hΦmono (P i) (P (i + 1))
      (le_trans hwP0 (hPmono (Nat.zero_le i)))
      (hPmono (Nat.le_succ i))
      (le_trans (hPmono (Nat.succ_le_of_lt hi)) (le_of_eq hPn))

end Work.ChenPlan.LinearSieve.Abel
