import Mathlib

namespace Work.Main.param

/-- Key arithmetic fact for the parameter choice: with `b ≥ 15` and `n > 2 ^ (b - 1)`,
the exponent `12 * 1729 + 3 + 1729 * b / 8` stays below `1728 * (b - 1)`, whence
`2 ^ (...) ≤ n ^ 1728`. -/
theorem two_pow_le_pow {b n : ℕ} (hb : 15 ≤ b) (hn : 2 ^ (b - 1) < n) :
    2 ^ (12 * 1729 + 3 + 1729 * b / 8) ≤ n ^ 1728 := by
  have hA : 12 * 1729 + 3 + 1729 * b / 8 ≤ (b - 1) * 1728 := by omega
  have hn' : 2 ^ (b - 1) ≤ n := le_of_lt hn
  calc 2 ^ (12 * 1729 + 3 + 1729 * b / 8) ≤ 2 ^ ((b - 1) * 1728) :=
        Nat.pow_le_pow_right (by omega) hA
    _ = (2 ^ (b - 1)) ^ 1728 := by rw [pow_mul]
    _ ≤ n ^ 1728 := Nat.pow_le_pow_left hn' 1728

end Work.Main.param
