import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.GeomSum

open scoped BigOperators

namespace Commons.Data.Nat

/-- For `1 ≤ q`, `(q - 1) * ∑_{i < n} q^i = q^n - 1` (the geometric sum in `ℕ`). -/
theorem geom_pred_mul_sum (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    (q - 1) * (∑ i ∈ Finset.range n, q ^ i) = q ^ n - 1 := by
  rw [mul_comm]
  exact geom_sum_mul_of_one_le hq n

end Commons.Data.Nat