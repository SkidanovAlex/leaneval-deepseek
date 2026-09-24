import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs

namespace Work.NumberTheory.Chen.BTermCount

/-- The dyadic block starts never overshoot the window top by more than `M`:
`blockStart M j = M * 2^j ≤ Y + M` for every block index `j < blockCount M Y`. -/
theorem blockStartLeAdd (M Y j : ℕ) (hM : 1 ≤ M) (hj : j < blockCount M Y) : blockStart M j ≤ Y + M := by
  rw [blockStart, blockCount] at *
  have hj' : j ≤ Nat.log 2 (Y / M + 1) := by omega
  have h2 : 2 ^ j ≤ Y / M + 1 := by
    calc 2 ^ j ≤ 2 ^ Nat.log 2 (Y / M + 1) := Nat.pow_le_pow_right (by norm_num) hj'
      _ ≤ Y / M + 1 := Nat.pow_log_le_self 2 (by simp)
  calc M * 2 ^ j ≤ M * (Y / M + 1) := Nat.mul_le_mul_left M h2
    _ = M * (Y / M) + M * 1 := by ring
    _ ≤ Y + M := by
        have := Nat.mul_div_le Y M
        omega

end Work.NumberTheory.Chen.BTermCount
