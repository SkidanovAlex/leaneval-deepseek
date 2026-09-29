import Mathlib

namespace Work.MainP

/-- For `0 < b`, `(a + b - 1) / b` is `⌈a/b⌉`, hence `a ≤ (a + b - 1) / b * b`. -/
theorem divCeilMulGe (a b : ℕ) (hb : 0 < b) : a ≤ (a + b - 1) / b * b := by
  have h := Nat.div_add_mod (a + b - 1) b
  have hr := Nat.mod_lt (a + b - 1) hb
  have hsub : (a + b - 1) - (b - 1) ≤ b * ((a + b - 1) / b) := by omega
  have ha : a = (a + b - 1) - (b - 1) := by omega
  rw [Nat.mul_comm]
  omega

end Work.MainP
