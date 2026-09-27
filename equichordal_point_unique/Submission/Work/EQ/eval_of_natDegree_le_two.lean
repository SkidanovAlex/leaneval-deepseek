import Mathlib

namespace Work.EQ

theorem eval_of_natDegree_le_two {R : Type*} [CommSemiring R] {p : Polynomial R} (h : p.natDegree ≤ 2)
    (x : R) : p.eval x = p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x ^ 2 := by
  rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]

end Work.EQ
