import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.WeylOps

/-- The *twisted product* of differential operators (the multiplication of the Ore
extension `K(X)[∂; d/dX]`), transported to the coefficient polynomial: `starMul D P Q`
has as its `n`-th coefficient the sum of `C(i,m)·P_i·(d/dX)^m(Q_j)` over all
`i, m, j` with `i - m + j = n`. -/
noncomputable def starMul {K : Type*} [Field K] (D : Derivation K (RatFunc K) (RatFunc K))
    (P Q : Polynomial (RatFunc K)) : Polynomial (RatFunc K) :=
  ∑ i ∈ P.support, ∑ j ∈ Q.support, ∑ m ∈ Finset.range (i + 1),
    Polynomial.monomial (i + j - m)
      ((Nat.choose i m : RatFunc K) * P.coeff i * ((D : RatFunc K → RatFunc K)^[m] (Q.coeff j)))

/-- Unfolding formula for `starMul`. -/
theorem starMul_def {K : Type*} [Field K] (D : Derivation K (RatFunc K) (RatFunc K))
    (P Q : Polynomial (RatFunc K)) :
    starMul D P Q
      = ∑ i ∈ P.support, ∑ j ∈ Q.support, ∑ m ∈ Finset.range (i + 1),
        Polynomial.monomial (i + j - m)
          ((Nat.choose i m : RatFunc K) * P.coeff i * ((D : RatFunc K → RatFunc K)^[m] (Q.coeff j))) := by
  rfl

end Commons.Algebra.WeylOps