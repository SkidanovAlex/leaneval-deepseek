import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Nat.Icc

open scoped BigOperators

theorem levelIndicator_sum {n : ℕ} (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 * n →
      (∑ j ∈ Finset.Icc 1 (2 * n - 1),
        (if k ≤ n then (if j < k then (1 : ℕ) else 0) else (if 2 * n + 1 - k ≤ j then (1 : ℕ) else 0))) = k - 1 := by
  intro k hk1 hk2
  by_cases hk : k ≤ n
  · -- Case `k ≤ n`: the summand is the indicator of `j < k`, so the sum counts
    -- `j ∈ [1, 2n-1]` with `j ≤ k-1`, i.e. exactly `k-1` values.
    simp only [hk, ↓reduceIte, Finset.sum_boole]
    have hf : (Finset.Icc 1 (2 * n - 1)).filter (fun j => j < k) = Finset.Icc 1 (k - 1) := by
      apply Finset.ext
      intro j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj1, _⟩, hjk⟩
        exact ⟨hj1, by omega⟩
      · rintro ⟨hj1, hjk⟩
        refine ⟨⟨hj1, ?_⟩, ?_⟩
        · omega
        · omega
    rw [hf, Nat.card_Icc]
    exact_mod_cast (by omega : (k - 1) + 1 - 1 = k - 1)
  · -- Case `k > n`: the summand is the indicator of `2n+1-k ≤ j`, so the sum
    -- counts `j ∈ [1, 2n-1]` with `j ≥ 2n+1-k`, i.e. `k-1` values.
    simp only [hk, ↓reduceIte, Finset.sum_boole]
    have hf : (Finset.Icc 1 (2 * n - 1)).filter (fun j => 2 * n + 1 - k ≤ j) =
        Finset.Icc (2 * n + 1 - k) (2 * n - 1) := by
      apply Finset.ext
      intro j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, hL⟩
        exact ⟨hL, hj2⟩
      · rintro ⟨hL, hj2⟩
        refine ⟨⟨?_, hj2⟩, hL⟩
        omega
    rw [hf, Nat.card_Icc]
    exact_mod_cast (by omega : (2 * n - 1) + 1 - (2 * n + 1 - k) = k - 1)

end Commons.Nat.Icc