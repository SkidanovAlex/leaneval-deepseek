import Mathlib

namespace Work.ZagC

theorem shift_down_sum (v : ℕ → ℚ) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 2), (n.choose m : ℚ) * (8 * (m : ℚ) ^ 2) * v (m - 1))
      = ∑ j ∈ Finset.range (n + 2), 8 * ((j : ℚ) + 1) ^ 2 * (n.choose (j + 1) : ℚ) * v j := by
  rw [Finset.sum_range_succ' (fun m => (n.choose m : ℚ) * (8 * (m : ℚ) ^ 2) * v (m - 1)) (n + 1),
      Finset.sum_range_succ (fun j => 8 * ((j : ℚ) + 1) ^ 2 * (n.choose (j + 1) : ℚ) * v j) (n + 1)]
  have h1 : (↑(n.choose 0) * (8 * ↑(0 : ℕ) ^ 2) * v (0 - 1) : ℚ) = 0 := by norm_num
  have h2 : (8 * (↑(n + 1) + 1) ^ 2 * ↑(n.choose (n + 1 + 1)) * v (n + 1) : ℚ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega : n < n + 1 + 1), Nat.cast_zero]
    ring
  simp only [h1, h2, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

end Work.ZagC
