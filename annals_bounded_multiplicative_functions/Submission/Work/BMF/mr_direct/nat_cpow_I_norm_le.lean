import Mathlib
import Submission.Work.BMF.norm_cpow_I_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- The complex power `n ^ (I * u)` of a natural number has modulus at most one,
for every real `u`.  (The value is `1` for `n = 0` and is a unit-modulus number
for `n ≥ 1`, so the bound `1` is sharp.) -/
theorem nat_cpow_I_norm_le (n : ℕ) (u : ℝ) :
    ‖(n : ℂ) ^ (Complex.I * (u : ℂ))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [Complex.cpow_def]
    split_ifs <;> simp
  · rw [Complex.norm_natCast_cpow_of_pos h]
    have hre : (Complex.I * (u : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.rpow_zero]

end Work.BMF.mr_direct
