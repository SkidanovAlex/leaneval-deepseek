import Mathlib.FieldTheory.RatFunc.Basic

namespace Commons.FieldTheory.RatFunc

/-- **The degree valuation at infinity**, as a `min`-valuation on `K(X)`: the `natDegree` of the
*denominator* minus the `natDegree` of the *numerator*, with value `⊤` at `0`.  This is
`- ordInfT` (`FieldTheory/RatFunc/ordInfT_def`) and is the tool the local/indicial analysis at the
point `∞` of the projective line uses, exactly as `Commons.FieldTheory.RatFunc.ordAtT` is used at a
finite point: `ordDegT X = -1`, `ordDegT (X⁻¹) = 1`, `ordDegT (x*y) = ordDegT x + ordDegT y`,
`min (ordDegT x) (ordDegT y) ≤ ordDegT (x + y)`, and `ordDegT (D x) = ordDegT x + 1` for the
standard derivation `D = d/dX`.  So the uniformizer at `∞` is `X⁻¹` (the counterpart of
`linFactor α = X - α`). -/
noncomputable def ordDegT {K : Type*} [Field K] (x : RatFunc K) : WithTop ℤ := by
  classical
  exact if x = 0 then ⊤
    else ((Polynomial.natDegree x.denom : ℤ) - (Polynomial.natDegree x.num : ℤ))

theorem ordDegT_def {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) :
    ordDegT x = ((Polynomial.natDegree x.denom : ℤ) - (Polynomial.natDegree x.num : ℤ)) := by
  simp [ordDegT, hx]

end Commons.FieldTheory.RatFunc