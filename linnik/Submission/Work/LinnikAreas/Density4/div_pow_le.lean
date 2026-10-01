import Mathlib

namespace Work.LinnikAreas.Density4

/-- For any `N` and `j`, dividing by `2^j` is at most twice dividing by `2^(j+1)`, plus one
(the extra half-step can only lose one unit of quotient). -/
theorem div_pow_le (N j : ℕ) : N / 2^j ≤ 2 * (N / 2^(j+1)) + 1 := by
  have h : N / 2^(j+1) = (N / 2^j) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h]
  have hdm := Nat.div_add_mod (N / 2^j) 2
  have hmod : (N / 2^j) % 2 ≤ 1 := by
    have := Nat.mod_lt (N / 2^j) (by norm_num : (0:ℕ) < 2)
    omega
  omega

end Work.LinnikAreas.Density4
