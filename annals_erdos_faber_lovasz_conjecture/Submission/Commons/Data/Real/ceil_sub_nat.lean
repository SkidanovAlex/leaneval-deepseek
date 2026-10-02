import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Data.Real

/-- For a real number `x` and a natural number `k`, the natural ceiling of
`x - k` is `k` less than the natural ceiling of `x` (with truncated
subtraction, as is forced by the codomain `ℕ`). -/
theorem ceil_sub_nat (x : ℝ) (k : ℕ) : ⌈x - k⌉₊ = ⌈x⌉₊ - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x - ((k + 1 : ℕ) : ℝ) = (x - (k : ℝ)) - 1 := by push_cast; ring
    rw [h, Nat.ceil_sub_one, ih, Nat.sub_sub]

end Commons.Data.Real