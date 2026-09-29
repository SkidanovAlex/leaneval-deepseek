import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.FieldTheory.RatFunc.ordAt_def

namespace Commons.FieldTheory.RatFunc

/-- On polynomials, the order of vanishing `ordAt` is the root multiplicity. -/
theorem ordAt_algebraMap {K : Type*} [Field K] (α : K) (p : Polynomial K) :
    ordAt α (algebraMap (Polynomial K) (RatFunc K) p)
      = (Polynomial.rootMultiplicity α p : ℤ) := by
  rw [ordAt_def, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, ← Polynomial.C_1]
  simp

end Commons.FieldTheory.RatFunc