import Submission.Commons.Algebra.Polynomial.wronskian_eq_zero_ratio

namespace Commons.Algebra.Polynomial

/-- Over a field of characteristic zero, if the Wronskian `P' * Q - P * Q'` vanishes with `Q ≠ 0`,
then `P` is a constant multiple of `Q`.  (Without coprimality: `P` and `Q` may share factors.)
Equivalently, a rational function `P/Q` with vanishing derivative is a constant. -/
theorem exists_eq_C_mul_of_derivative_mul_eq {K : Type*} [Field K] [CharZero K]
    {P Q : Polynomial K} (hQ : Q ≠ 0)
    (h : Polynomial.derivative P * Q = P * Polynomial.derivative Q) :
    ∃ c : K, P = Polynomial.C c * Q :=
  wronskian_eq_zero_ratio hQ h

end Commons.Algebra.Polynomial
