import Mathlib

namespace Work.WilE9G.Assembly

theorem poly_eval_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  apply Finset.sum_le_sum
  intro k _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

end Work.WilE9G.Assembly
