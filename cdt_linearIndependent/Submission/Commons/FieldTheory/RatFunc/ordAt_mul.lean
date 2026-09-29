import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Submission.Commons.FieldTheory.RatFunc.ordAt_def

namespace Commons.FieldTheory.RatFunc

open Polynomial

/-- `rootMultiplicity` is additive over a product of nonzero polynomials. -/
private theorem rootMultiplicity_mul_of_ne_zero {K : Type*} [Field K] (α : K)
    {p q : Polynomial K} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).rootMultiplicity α = p.rootMultiplicity α + q.rootMultiplicity α :=
  Polynomial.rootMultiplicity_mul (mul_ne_zero hp hq)

/-- The order of vanishing is additive (a valuation on the multiplicative group of `K(X)`). -/
theorem ordAt_mul {K : Type*} [Field K] (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt α (x * y) = ordAt α x + ordAt α y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  -- The cross-multiplication identity for numerators and denominators.
  have key := congrArg (fun p : Polynomial K => p.rootMultiplicity α)
    (RatFunc.num_denom_mul x y)
  rw [rootMultiplicity_mul_of_ne_zero α (RatFunc.num_ne_zero hxy)
        (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)),
      rootMultiplicity_mul_of_ne_zero α (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y),
      rootMultiplicity_mul_of_ne_zero α
        (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
        (RatFunc.denom_ne_zero (x * y)),
      rootMultiplicity_mul_of_ne_zero α (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy)] at key
  -- Cast the multiplicity identity to `ℤ` and linearize.
  have keyZ : ((x * y).num.rootMultiplicity α : ℤ)
        + ((x.denom.rootMultiplicity α : ℤ) + (y.denom.rootMultiplicity α : ℤ))
      = ((x.num.rootMultiplicity α : ℤ) + (y.num.rootMultiplicity α : ℤ))
        + ((x * y).denom.rootMultiplicity α : ℤ) := by
    exact_mod_cast key
  rw [ordAt_def, ordAt_def, ordAt_def]
  linarith

end Commons.FieldTheory.RatFunc