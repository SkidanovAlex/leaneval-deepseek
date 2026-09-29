import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- Over a field of characteristic `0`, the formal derivative lowers the
multiplicity of `α` as a root by exactly one when it is positive, and never
below `rootMultiplicity - 1`. -/
theorem le_rootMultiplicity_derivative {K : Type*} [Field K] [CharZero K]
    (α : K) {p : Polynomial K} (hp : p ≠ 0) :
    Polynomial.rootMultiplicity α p ≤ Polynomial.rootMultiplicity α p.derivative + 1 := by
  have h := Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity p α
  omega

end Commons.Algebra.Polynomial