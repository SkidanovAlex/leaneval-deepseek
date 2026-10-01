import Mathlib.Algebra.Polynomial.Taylor

namespace Commons.Algebra.Polynomial

open scoped BigOperators

theorem eval_add_eq_sum_hasseDeriv {R : Type*} [CommSemiring R]
    (f : Polynomial R) (x y : R) :
    Polynomial.eval (x + y) f
      = ∑ n ∈ Finset.range (f.natDegree + 1),
          Polynomial.eval x (Polynomial.hasseDeriv n f) * y ^ n := by
  rw [add_comm x y, ← Polynomial.taylor_eval x f y, Polynomial.eval_eq_sum_range,
      Polynomial.natDegree_taylor]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.taylor_coeff]

end Commons.Algebra.Polynomial