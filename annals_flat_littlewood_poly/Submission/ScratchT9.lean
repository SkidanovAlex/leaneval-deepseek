import Mathlib

example (k : ℕ) (hk : k ≤ 4) :
    (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (1 / (2 : ℝ) ^ (9 * (k - i))))) +
      (∑ i ∈ Finset.range k, ((k.choose i : ℝ) * (2 ^ i) * (1 / (2 : ℝ) ^ (9 * (k - i))))) ≤ 1 / 8 := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num [Finset.sum_range_succ, show Nat.choose 1 0 = 1 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 2 0 = 1 by native_decide,
      show Nat.choose 2 1 = 2 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 3 0 = 1 by native_decide,
      show Nat.choose 3 1 = 3 by native_decide, show Nat.choose 3 2 = 3 by native_decide]
  · norm_num [Finset.sum_range_succ, show Nat.choose 4 0 = 1 by native_decide,
      show Nat.choose 4 1 = 4 by native_decide, show Nat.choose 4 2 = 6 by native_decide,
      show Nat.choose 4 3 = 4 by native_decide]
