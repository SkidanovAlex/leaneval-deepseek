import Mathlib

namespace Work.WilE9.Ift.OneShot

/-- Evaluation of a polynomial with nonnegative integer coefficients is monotone on `ℕ`. -/
theorem poly_eval_le {p : Polynomial ℕ} {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

end Work.WilE9.Ift.OneShot
