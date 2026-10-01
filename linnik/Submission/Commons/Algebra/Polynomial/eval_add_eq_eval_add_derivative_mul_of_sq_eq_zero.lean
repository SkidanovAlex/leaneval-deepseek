import Mathlib.Algebra.Polynomial.Taylor

namespace Commons.Algebra.Polynomial

theorem eval_add_eq_eval_add_derivative_mul_of_sq_eq_zero {R : Type*} [CommRing R]
    (P : Polynomial R) {u δ : R} (hδ : δ ^ 2 = 0) :
    P.eval (u + δ) = P.eval u + (Polynomial.derivative P).eval u * δ := by
  exact Polynomial.eval_add_of_sq_eq_zero P u δ hδ

end Commons.Algebra.Polynomial