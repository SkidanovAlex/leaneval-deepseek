import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

theorem derivative_iter_rootMultiplicity_eval_ne_zero {K : Type*} [Field K] [CharZero K]
    (p : Polynomial K) (hp : p ≠ 0) (a : K) :
    ((Polynomial.derivative^[Polynomial.rootMultiplicity a p]) p).eval a ≠ 0 := by
  rw [Polynomial.eval_iterate_derivative_rootMultiplicity]
  rw [nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp)

end Commons.Algebra.Polynomial