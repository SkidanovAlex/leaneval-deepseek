import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.WeylOps

/-- The differential operator `Σ_i P.coeff i · (d/dX)^i` attached to a polynomial
`P ∈ K(X)[∂]`, acting on the field of rational functions `K(X) = RatFunc K`
(the Weyl algebra `K(X)[∂]` represented on `K(X)` itself). -/
noncomputable def opOf {K : Type*} [Field K] (D : Derivation K (RatFunc K) (RatFunc K))
    (P : Polynomial (RatFunc K)) : Module.End K (RatFunc K) :=
  ∑ i ∈ P.support, (LinearMap.mulLeft K (P.coeff i)).comp (D.toLinearMap ^ i)

/-- Unfolding formula for `opOf`. -/
theorem opOf_def {K : Type*} [Field K] (D : Derivation K (RatFunc K) (RatFunc K))
    (P : Polynomial (RatFunc K)) :
    opOf D P = ∑ i ∈ P.support, (LinearMap.mulLeft K (P.coeff i)).comp (D.toLinearMap ^ i) := by
  rfl

end Commons.Algebra.WeylOps