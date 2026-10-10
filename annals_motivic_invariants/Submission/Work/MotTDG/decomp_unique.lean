import Mathlib
import Submission.Work.MotTDG.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `decomp_unique`: uniqueness of the `p(x) + q(x)·y` decomposition in a Weierstrass function field

Let `E` be a Weierstrass curve over a field `L` and `x = genX E`, `y = genY E` the two standard
generators of the function field `L(E)`.  This file proves that the representation of an element
of `L(E)` as `p(x) + q(x)·y` with `p, q ∈ L[X]` is unique: if `p(x) + q(x)·y = 0` in `L(E)`, then
`p = 0` and `q = 0`.

The mathematical content is entirely the corresponding statement in the *affine coordinate ring*
`A = L[E] = L[X,Y]/(W_E)`, where it is `WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero`:
the Weierstrass polynomial `Y² + (a₁X+a₃)Y - (X³+a₂X²+a₄X+a₆)` has odd `X`-degree, hence is
irreducible over `L[X]`, so `A` is a domain and `1, y` is an `L[X]`-basis of `A`
(`CoordinateRing.basis`), whence `p • 1 + q • mk Y = 0 → p = 0 ∧ q = 0`.

Two bridges are needed:

* `L[E] → L(E) = Frac(L[E])` is injective (`IsFractionRing.injective`), so an identity that holds
  in the function field holds already in the coordinate ring;
* `aeval (mk (C X)) r = r • 1` in the coordinate ring (`aeval_mk_C_X`), because `mk (C X)` is the
  image of `X` under `algebraMap L[X] L[E]` (`mk_C_X_eq_algebraMap_X`) and `aeval X` is the
  identity on `L[X]`.

This is the input the TDG node needs for "the Weierstrass pair `(x', y')` of a point of `E` over
`L(E)` determines `x', y'`: a relation `p(x') + q(x')y' = 0` can only be the trivial one.
-/

set_option autoImplicit false

namespace Work.MotTDG

open WeierstrassCurve WeierstrassCurve.Affine

variable {L : Type*} [Field L]

/-- The class of `X` in the affine coordinate ring of `E` is the image of `X ∈ L[X]` under the
structure map `algebraMap L[X] L[E]` (`AdjoinRoot.of`). -/
theorem mk_C_X_eq_algebraMap_X (E : WeierstrassCurve L) :
    CoordinateRing.mk E (Polynomial.C Polynomial.X)
      = algebraMap (Polynomial L) (CoordinateRing E) Polynomial.X := by
  rw [AdjoinRoot.algebraMap_eq]
  rfl

/-- `Polynomial.aeval` at the class of `X` in the affine coordinate ring is the `L[X]`-scalar
multiplication by the polynomial: `aeval xA r = r • 1` in `L[E]`. -/
theorem aeval_mk_C_X (E : WeierstrassCurve L) (r : Polynomial L) :
    Polynomial.aeval (CoordinateRing.mk E (Polynomial.C Polynomial.X)) r
      = r • (1 : CoordinateRing E) := by
  rw [mk_C_X_eq_algebraMap_X E, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_X_left_apply, AdjoinRoot.algebraMap_eq, CoordinateRing.smul, mul_one]
  rfl

/-- **Uniqueness of the `p(x) + q(x)·y` decomposition**: if `p(x) + q(x)·y = 0` in the function
field `L(E)` of a Weierstrass curve `E` over a field `L`, then `p = q = 0`. -/
theorem decomp_unique {L : Type*} [Field L] (E : WeierstrassCurve L) {p q : Polynomial L}
    (h : Polynomial.aeval (Work.MotV.genX E) p
        + Polynomial.aeval (Work.MotV.genX E) q * Work.MotV.genY E = 0) :
    p = 0 ∧ q = 0 := by
  -- The identity, read in the affine coordinate ring `A = L[E]` (`Work.MotV.genX`/`genY` are the
  -- images of `mk (C X)` and `mk X` under `L[E] → L(E)`).
  have key : Polynomial.aeval (CoordinateRing.mk E (Polynomial.C Polynomial.X)) p
      + Polynomial.aeval (CoordinateRing.mk E (Polynomial.C Polynomial.X)) q
        * CoordinateRing.mk E Polynomial.X = 0 := by
    apply IsFractionRing.injective (CoordinateRing E) (FunctionField E)
    rw [map_add, map_mul, map_zero]
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_algebraMap_apply]
    exact h
  -- Rewrite `aeval xA r` as the `L[X]`-scalar multiple `r • 1` and apply the basis lemma.
  have key' : p • (1 : CoordinateRing E) + q • CoordinateRing.mk E Polynomial.X = 0 := by
    rw [← one_mul (CoordinateRing.mk E Polynomial.X), ← smul_mul_assoc, ← aeval_mk_C_X E q,
      ← aeval_mk_C_X E p]
    exact key
  exact CoordinateRing.smul_basis_eq_zero key'

end Work.MotTDG
