/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV
-/
import Mathlib
import Submission.Work.MotC2.TranslationDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The generic point of a Weierstrass curve is not 2-torsion

For a Weierstrass curve `E` over a field `N` of characteristic `≠ 2`, the function
`2y + a₁x + a₃` is not zero in the function field `N(E)`.  Equivalently, the generic point of
`E` is not a 2-torsion point (there is no "universal solution" of `y = negY x y`).

The mathematical content is a degree count.  In the affine coordinate ring
`N[X,Y]/(W_E)` the class of

`C 2 * Y + C (C a₁ * X) + C (C a₃)`

is the relevant element; it is a nonzero polynomial in `Y` of `Y`-degree `≤ 1`, while the
Weierstrass polynomial `W_E` is monic of `Y`-degree `2`, so it cannot be divisible by `W_E`.
This is formalised through the `N[X]`-basis `{1, y}` of the coordinate ring
(`WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero`): writing the element as
`p • 1 + q • mk Y` with `q = C 2` forces `q = 0`, contradicting `2 ≠ 0`.

## Main result

* `Work.MotV.two_mul_genY_add_ne_zero`
-/

open WeierstrassCurve.Affine Polynomial

namespace Work.MotV

/-- The structural algebra map `N → N[X,Y]/(W_E)` factors through the polynomial ring: it sends
`a` to the class of the constant polynomial `C (C a)`. -/
lemma algebraMap_coord_eq_mk_C_C {N : Type*} [Field N] (E : WeierstrassCurve N) (a : N) :
    algebraMap N (Work.MotC2.Coord E) a = CoordinateRing.mk E (Polynomial.C (Polynomial.C a)) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, AdjoinRoot.of, RingHom.comp_apply,
    Polynomial.algebraMap_eq]

/-- **The coordinate-ring form.**  For a field `N` of characteristic `≠ 2` the class of
`2Y + a₁X + a₃` in `N[X,Y]/(W_E)` is nonzero. -/
lemma two_mul_coordY_add_ne_zero {N : Type*} [Field N] (E : WeierstrassCurve N)
    (h2 : (2 : N) ≠ 0) :
    2 * Work.MotC2.coordY E + algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordX E +
      algebraMap N (Work.MotC2.Coord E) E.a₃ ≠ 0 := by
  have hY : (2 : Work.MotC2.Coord E) * Work.MotC2.coordY E
      = (Polynomial.C (2 : N)) • (CoordinateRing.mk E Polynomial.X) := by
    rw [CoordinateRing.smul, show (2 : Work.MotC2.Coord E)
        = algebraMap N (Work.MotC2.Coord E) (2 : N) from rfl,
      algebraMap_coord_eq_mk_C_C, Work.MotC2.coordY_eq_mk, ← map_mul]
  have hX : algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordX E
      = (Polynomial.C E.a₁ * Polynomial.X) • (1 : Work.MotC2.Coord E) := by
    rw [CoordinateRing.smul, mul_one, algebraMap_coord_eq_mk_C_C, Work.MotC2.coordX_eq_mk,
      ← map_mul, ← Polynomial.C_mul]
  have hC : algebraMap N (Work.MotC2.Coord E) E.a₃
      = (Polynomial.C E.a₃) • (1 : Work.MotC2.Coord E) := by
    rw [CoordinateRing.smul, mul_one, ← algebraMap_coord_eq_mk_C_C]
  -- Rewrite the element in the `N[X]`-basis `{1, y}` of the coordinate ring.
  have hkey : 2 * Work.MotC2.coordY E + algebraMap N (Work.MotC2.Coord E) E.a₁
        * Work.MotC2.coordX E + algebraMap N (Work.MotC2.Coord E) E.a₃
      = (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) • (1 : Work.MotC2.Coord E)
        + (Polynomial.C (2 : N)) • (CoordinateRing.mk E Polynomial.X) := by
    rw [hY, hX, hC, add_smul]
    abel
  intro h
  have hzero : (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) • (1 : Work.MotC2.Coord E)
      + (Polynomial.C (2 : N)) • (CoordinateRing.mk E Polynomial.X) = 0 := by
    rw [← hkey]
    exact h
  obtain ⟨-, hq⟩ := CoordinateRing.smul_basis_eq_zero hzero
  exact (Polynomial.C_ne_zero.mpr h2) hq

/-- **The generic point is not 2-torsion.**  Over a field `N` of characteristic `≠ 2`, the function
`2y + a₁x + a₃` is not identically zero on a Weierstrass curve `E`; equivalently the generic point
of `E` is not killed by doubling. -/
theorem two_mul_genY_add_ne_zero {N : Type*} [Field N] (E : WeierstrassCurve N)
    (h2 : (2 : N) ≠ 0) :
    2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ ≠ 0 := by
  have htrans : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E)
      (2 * Work.MotC2.coordY E + algebraMap N (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordX E
        + algebraMap N (Work.MotC2.Coord E) E.a₃)
      = 2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E
        + algebraMap N (Work.MotC2.Func E) E.a₃ := by
    simp only [map_add, map_mul, map_ofNat, Work.MotC2.genX, Work.MotC2.genY,
      IsScalarTower.algebraMap_apply N (Work.MotC2.Coord E) (Work.MotC2.Func E)]
  intro h
  refine two_mul_coordY_add_ne_zero E h2
    (IsFractionRing.injective (Work.MotC2.Coord E) (Work.MotC2.Func E) ?_)
  rw [htrans, map_zero]
  exact h

end Work.MotV
