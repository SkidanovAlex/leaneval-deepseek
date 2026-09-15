import Mathlib

namespace Commons.Combinatorics.LevelBlocks

theorem div_mul_div_eq {n M m i : ℕ} (hM : 0 < M) :
    (n * M * (2 * i + 1)) / (2 * m) / M = (n * (2 * i + 1)) / (2 * m) := by
  rw [Nat.div_div_eq_div_mul]
  have h : n * M * (2 * i + 1) = n * (2 * i + 1) * M := by ring
  rw [h, Nat.mul_div_mul_right _ _ hM]

end Commons.Combinatorics.LevelBlocks
