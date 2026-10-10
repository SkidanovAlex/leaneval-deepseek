import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- A root in `RatFunc L` of a monic quadratic `T² + bT + d` with coefficients in `L[X]`
is itself a polynomial. -/
theorem RatFuncIntegral {L : Type*} [Field L] (x : RatFunc L)
    (b d : Polynomial L)
    (h : x ^ 2 + algebraMap (Polynomial L) (RatFunc L) b * x
          + algebraMap (Polynomial L) (RatFunc L) d = 0) :
    ∃ P : Polynomial L, algebraMap (Polynomial L) (RatFunc L) P = x := by
  -- `x` is a root of the monic polynomial `T² + bT + d` over `L[X]`, hence integral.
  have hint : IsIntegral (Polynomial L) x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C d, ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact h
  -- `L[X]` is a UFD, hence integrally closed in its fraction field `RatFunc L`.
  exact (IsIntegrallyClosed.isIntegral_iff (R := Polynomial L) (K := RatFunc L) (x := x)).mp hint

end Work.MotC2
