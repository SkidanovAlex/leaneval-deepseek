import Mathlib.RingTheory.Derivation.Basic

namespace Commons.RingTheory.Derivation

/-- The chain rule for a derivation applied to a polynomial: if `D x` is the image in `L` of a
constant `a` of the base field `K`, then `D (P(x)) = a * P'(x)` for every `P : K[X]`. -/
theorem aeval_derivative {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Derivation K L L) (x : L) (a : K) (hx : D x = algebraMap K L a) (P : Polynomial K) :
    D ((Polynomial.aeval x) P)
      = algebraMap K L a * (Polynomial.aeval x) (Polynomial.derivative P) := by
  rw [D.map_aeval, hx, smul_eq_mul, mul_comm]

end Commons.RingTheory.Derivation