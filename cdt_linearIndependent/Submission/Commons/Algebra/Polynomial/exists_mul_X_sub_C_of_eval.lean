import Mathlib.Algebra.Polynomial.Div

open Polynomial

namespace Commons.Algebra.Polynomial

lemma exists_mul_X_sub_C_of_eval {R : Type*} [CommRing R] (q : R[X]) (a : R) :
    ∃ Q : R[X], q - C (q.eval a) = (X - C a) * Q := by
  exact Polynomial.X_sub_C_dvd_sub_C_eval

end Commons.Algebra.Polynomial