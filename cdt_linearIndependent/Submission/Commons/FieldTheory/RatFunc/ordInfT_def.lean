import Mathlib.FieldTheory.RatFunc.Basic

namespace Commons.FieldTheory.RatFunc

/-- **The order at infinity** of a rational function: the `natDegree` of the numerator minus the
`natDegree` of the denominator, with value `⊤` at `0`.  On `K(X)` viewed as the function field of
the projective line this is the valuation at the point `∞`; it satisfies `ordInfT X = 1`,
`ordInfT (x*y) = ordInfT x + ordInfT y`, the `min` rule for sums, and `ordInfT (D x) = ordInfT x - 1`
for the standard derivation `D = d/dX`.  It is the exact counterpart of
`Commons.FieldTheory.RatFunc.ordAtT` at the other end of the projective line, and it is what the
local/indicial analysis at `∞` (the bound `N_∞ ≤ 5` of CDT arXiv:2408.15403, §"Products of two
logarithms") uses. -/
noncomputable def ordInfT {K : Type*} [Field K] (x : RatFunc K) : WithTop ℤ := by
  classical
  exact if x = 0 then ⊤
    else ((Polynomial.natDegree x.num : ℤ) - (Polynomial.natDegree x.denom : ℤ))

theorem ordInfT_def {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) :
    ordInfT x = ((Polynomial.natDegree x.num : ℤ) - (Polynomial.natDegree x.denom : ℤ)) := by simp [ordInfT, hx]

end Commons.FieldTheory.RatFunc