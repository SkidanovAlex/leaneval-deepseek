import Mathlib

namespace Commons.Data.Nat

theorem gcd_sub_reflection (m c : ℕ) (h : c ≤ m) : m.gcd (m - c) = c.gcd m := by
  rw [Nat.gcd_self_sub_right h, Nat.gcd_comm]

end Commons.Data.Nat
