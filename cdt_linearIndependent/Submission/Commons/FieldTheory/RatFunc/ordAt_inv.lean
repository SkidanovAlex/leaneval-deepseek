import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.FieldTheory.RatFunc.ordAt_def

namespace Commons.FieldTheory.RatFunc

open Polynomial

/-- The multiplicity of `α` as a root of a polynomial is invariant under association: a unit of
`K[X]` is a nonzero constant `C r`, and multiplication by such a constant does not change the
order of vanishing at `α`. -/
lemma rootMultiplicity_eq_of_associated {K : Type*} [Field K] {α : K} {p q : Polynomial K}
    (h : Associated p q) (hp : p ≠ 0) :
    p.rootMultiplicity α = q.rootMultiplicity α := by
  obtain ⟨u, hu⟩ := h
  have hu_ne : (u : Polynomial K) ≠ 0 := Units.ne_zero u
  have hpu : p * (u : Polynomial K) ≠ 0 := mul_ne_zero hp hu_ne
  have hzero : (u : Polynomial K).rootMultiplicity α = 0 := by
    obtain ⟨r, _, hCr⟩ := Polynomial.isUnit_iff.mp u.isUnit
    rw [← hCr]
    exact Polynomial.rootMultiplicity_C r α
  rw [← hu, Polynomial.rootMultiplicity_mul hpu, hzero, add_zero]

/-- The order of vanishing changes sign under inversion. -/
theorem ordAt_inv {K : Type*} [Field K] (α : K) {x : RatFunc K} (hx : x ≠ 0) :
    ordAt α x⁻¹ = -ordAt α x := by
  have h1 : ((x⁻¹).num).rootMultiplicity α = x.denom.rootMultiplicity α :=
    rootMultiplicity_eq_of_associated (RatFunc.associated_num_inv hx)
      (RatFunc.num_ne_zero (inv_ne_zero hx))
  have h2 : ((x⁻¹).denom).rootMultiplicity α = x.num.rootMultiplicity α :=
    rootMultiplicity_eq_of_associated (RatFunc.associated_denom_inv hx)
      (RatFunc.denom_ne_zero x⁻¹)
  rw [ordAt_def, ordAt_def, h1, h2]
  ring

end Commons.FieldTheory.RatFunc