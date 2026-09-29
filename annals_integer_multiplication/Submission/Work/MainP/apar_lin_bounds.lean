import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-- For `b ≥ 2^61` one has `2^31 ≤ b / 2^30` (since `2^61 = 2^31 · 2^30`). -/
theorem two_pow_31_le_div (b : ℕ) (hb : 2 ^ 61 ≤ b) : 2 ^ 31 ≤ b / 2 ^ 30 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2 ^ 30)]
  calc 2 ^ 31 * 2 ^ 30 = 2 ^ 61 := by norm_num
    _ ≤ b := hb

/-- The two linear bounds turning `α² ≤ 17970·(b/2^30 + 1) + 1` into the strict inequalities of
`AparFacts`: for `b ≥ 2^61`, `17970·(b/2^30 + 1) + 1 < 6b` and `3458·(17970·(b/2^30 + 1) + 1) + 13 < b`.
Writing `q = b / 2^30 ≥ 1`, it suffices that `17970q + 17971 < 6·2^30·q` and `3458(17970q + 17971) + 13 < 2^30·q`.
Namespace `Work.MainP`, importing `Submission.Work.MainP.basic`. -/
theorem apar_lin_bounds (b : ℕ) (hb : 2 ^ 61 ≤ b) :
    17970 * (b / 2 ^ 30 + 1) + 1 < 6 * b ∧
    3458 * (17970 * (b / 2 ^ 30 + 1) + 1) + 13 < b := by
  have hq : 2 ^ 31 ≤ b / 2 ^ 30 := two_pow_31_le_div b hb
  have hdiv : (b / 2 ^ 30) * 2 ^ 30 ≤ b := Nat.div_mul_le_self b (2 ^ 30)
  constructor <;> nlinarith [hq, hdiv]

end Work.MainP
