import Mathlib

namespace Commons.Algebra.Nat

theorem div_two_succ_le {n : ℕ} (hn : 1 ≤ n) : (n + 2) / 2 ≤ n := by
  omega

end Commons.Algebra.Nat
