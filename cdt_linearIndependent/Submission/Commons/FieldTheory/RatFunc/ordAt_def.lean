import Mathlib.FieldTheory.RatFunc.Basic
import Submission.Commons.RingTheory.RatFunc.iterate_deriv_algebraMap

namespace Commons.FieldTheory.RatFunc

/-- **Order of vanishing at `α`** of a rational function `x ∈ K(X)`: the multiplicity of `α` as
a root of the numerator minus its multiplicity as a root of the denominator.  Negative values
encode poles (`-ordAt` being the pole order). -/
noncomputable def ordAt {K : Type*} [Field K] (α : K) (x : RatFunc K) : ℤ :=
  (Polynomial.rootMultiplicity α x.num : ℤ) - (Polynomial.rootMultiplicity α x.denom : ℤ)

/-- Unfolding formula for `ordAt`. -/
theorem ordAt_def {K : Type*} [Field K] (α : K) (x : RatFunc K) :
    ordAt α x
      = (Polynomial.rootMultiplicity α x.num : ℤ) - (Polynomial.rootMultiplicity α x.denom : ℤ) := by
  rfl

end Commons.FieldTheory.RatFunc