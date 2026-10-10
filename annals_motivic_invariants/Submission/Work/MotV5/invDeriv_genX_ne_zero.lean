import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Nonvanishing of the invariant derivation on `x`

For a Weierstrass curve `E` over a field `N` of characteristic `5`, the value of the invariant
derivation on the coordinate `x`,

`2y + a₁x + a₃`,

is nonzero in the function field `N(E)`.  Equivalently, the Weierstrass polynomial
`Y² + (a₁X + a₃)Y - (X³ + a₂X² + a₄X + a₆)` has no root which is linear in `Y`:
in the coordinate ring `N[X,Y]/(W_E)` the class of `2Y + a₁X + a₃` is nonzero because `W_E` is
monic of `Y`-degree two while `2Y + a₁X + a₃` has `Y`-degree at most one, and `2 ≠ 0` in
characteristic `5`; the fraction field map `N[X,Y]/(W_E) → N(E)` is injective since the coordinate
ring is a domain.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV5

/-- In characteristic `5`, the function `2y + a₁x + a₃` of an elliptic curve is nonzero in the
function field. -/
theorem invDeriv_genX_ne_zero {N : Type*} [Field N] [CharP N 5] (E : WeierstrassCurve N) :
    2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ ≠ 0 := by
  intro h
  -- The coordinate ring `N[X,Y]/(W_E)` is a domain, so it embeds in its fraction field.
  have hinj : Function.Injective (algebraMap (MotC2.Coord E) (MotC2.Func E)) :=
    IsFractionRing.injective _ _
  have h1 : algebraMap (MotC2.Coord E) (MotC2.Func E) (algebraMap N (MotC2.Coord E) E.a₁)
      = algebraMap N (MotC2.Func E) E.a₁ :=
    (IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E) E.a₁).symm
  have h3 : algebraMap (MotC2.Coord E) (MotC2.Func E) (algebraMap N (MotC2.Coord E) E.a₃)
      = algebraMap N (MotC2.Func E) E.a₃ :=
    (IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E) E.a₃).symm
  have heq : algebraMap (MotC2.Coord E) (MotC2.Func E)
        ((2 : MotC2.Coord E) * MotC2.coordY E + algebraMap N (MotC2.Coord E) E.a₁ * MotC2.coordX E +
          algebraMap N (MotC2.Coord E) E.a₃)
        = 2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
          algebraMap N (MotC2.Func E) E.a₃ := by
      simp only [map_add, map_mul, map_ofNat, MotC2.genX, MotC2.genY, h1, h3]
  -- Reduce the nonvanishing to the coordinate ring.
  have hz : (2 : MotC2.Coord E) * MotC2.coordY E + algebraMap N (MotC2.Coord E) E.a₁ * MotC2.coordX E +
        algebraMap N (MotC2.Coord E) E.a₃ = 0 := by
    apply hinj
    rw [map_zero, heq]
    exact h
  -- Write it in the `N[X]`-basis `{1, Y}` of the coordinate ring.
  have hcoordX : algebraMap (Polynomial N) (MotC2.Coord E) Polynomial.X = MotC2.coordX E := by
    rw [MotC2.coordX, AdjoinRoot.algebraMap_eq]
  have hcoordY : (CoordinateRing.mk E Polynomial.X : MotC2.Coord E) = MotC2.coordY E :=
    (MotC2.coordY_eq_mk E).symm
  have ha1 : algebraMap (Polynomial N) (MotC2.Coord E) (Polynomial.C E.a₁) =
      algebraMap N (MotC2.Coord E) E.a₁ :=
    (IsScalarTower.algebraMap_apply N (Polynomial N) (MotC2.Coord E) E.a₁).symm
  have ha3 : algebraMap (Polynomial N) (MotC2.Coord E) (Polynomial.C E.a₃) =
      algebraMap N (MotC2.Coord E) E.a₃ :=
    (IsScalarTower.algebraMap_apply N (Polynomial N) (MotC2.Coord E) E.a₃).symm
  have hpq : (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃ : Polynomial N) • (1 : MotC2.Coord E)
      + (2 : Polynomial N) • CoordinateRing.mk E Polynomial.X = 0 := by
    rw [hcoordY, ← hz]
    simp only [Algebra.smul_def, map_add, map_mul, map_ofNat, mul_one, hcoordX, ha1, ha3]
    first | refl_ring1 | ring
  -- But the `Y`-coordinate `2` of this element is nonzero, since `char N = 5`.
  have h2NX : (2 : Polynomial N) ≠ 0 := by
    show ((2 : ℕ) : Polynomial N) ≠ 0
    intro hh
    rw [CharP.cast_eq_zero_iff (Polynomial N) 5 2] at hh
    exact absurd hh (by decide)
  exact h2NX (CoordinateRing.smul_basis_eq_zero (W' := E) hpq).2

end Work.MotV5
