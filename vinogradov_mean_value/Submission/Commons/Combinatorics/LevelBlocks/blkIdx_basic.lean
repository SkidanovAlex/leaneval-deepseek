import Mathlib

namespace Commons.Combinatorics.LevelBlocks

theorem blkIdx_basic {m n i : ℕ} (hm : 0 < m) (hn : 0 < n) (hi : i < m) :
    (n * (2 * i + 1)) / (2 * m) < n ∧ (m * (2 * i + 1)) / (2 * m) = i := by
  have hm2 : 0 < 2 * m := by omega
  have hlt : 2 * i + 1 < 2 * m := by omega
  constructor
  · rw [Nat.div_lt_iff_lt_mul hm2]
    exact Nat.mul_lt_mul_of_pos_left hlt hn
  · rw [show m * (2 * i + 1) = 2 * m * i + m by ring]
    rw [Nat.div_eq_of_lt_le (by nlinarith [hm]) (by nlinarith [hm])]

end Commons.Combinatorics.LevelBlocks
