import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic

namespace Commons.Data.Nat

theorem nat_div_le_real_div (L d : ℕ) : ((L / d : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) := by
  exact Nat.cast_div_le (α := ℝ)

end Commons.Data.Nat