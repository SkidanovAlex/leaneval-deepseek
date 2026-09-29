import Mathlib

namespace Work.Layout

theorem size_two_pow_sub_one (k : ℕ) : (2 ^ k - 1).size = k := by
  rcases k with _ | k
  · simp
  · have h1 : (2 ^ (k + 1) - 1).size ≤ k + 1 := by
      rw [Nat.size_le]
      exact Nat.sub_lt (by positivity) (by norm_num)
    have h2 : k < (2 ^ (k + 1) - 1).size := by
      rw [Nat.lt_size]
      rw [Nat.le_sub_one_iff_lt (by positivity)]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
    omega

end Work.Layout
