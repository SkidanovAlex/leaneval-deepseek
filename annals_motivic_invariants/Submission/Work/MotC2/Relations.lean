/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The Weierstrass relations for `Work.MotC2`

This file collects the basic relations satisfied by the objects introduced in
`Submission/Work/MotC2/Defs.lean`:

* `coordY_sq_relation`: the Weierstrass equation in the affine coordinate ring `L[X,Y]/(W_E)`;
* `genY_sq_relation`: the same relation in the function field `L(E)`, i.e. the affine Weierstrass
  equation for the generic point;
* `Equation (baseE E) (genX E) (genY E)`: the same statement phrased with
  `WeierstrassCurve.Affine.Equation` after pushing the coefficients forward to `L(E)`;
* `infW_sq_relation`: the Weierstrass equation in the chart at infinity, in the coordinates
  `u = 1/x`, `w = y/x²`;
* every `L`-rational point of an elliptic curve is nonsingular.

## Tags

elliptic curve, function field, Weierstrass equation, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-! ## The Weierstrass relation in the coordinate ring -/

/-- The Weierstrass relation `y² + (a₁x + a₃)y = x³ + a₂x² + a₄x + a₆` in the affine coordinate
ring `L[X,Y]/(W_E)`, for `x` and `y` the classes of `X` and `Y`. -/
theorem coordY_sq_relation (E : WeierstrassCurve L) :
    (coordY E) ^ 2 + (algebraMap L (Coord E) E.a₁ * coordX E + algebraMap L (Coord E) E.a₃) *
        coordY E =
      (coordX E) ^ 3 + algebraMap L (Coord E) E.a₂ * (coordX E) ^ 2 +
        algebraMap L (Coord E) E.a₄ * coordX E + algebraMap L (Coord E) E.a₆ := by
  have h := AdjoinRoot.mk_self (f := polynomial E)
  rw [WeierstrassCurve.Affine.polynomial] at h
  simp only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  rw [← of_poly_C, ← of_poly_C, ← of_poly_C, ← of_poly_C, ← of_poly_C]
  exact sub_eq_zero.mp h

/-! ## The Weierstrass relation in the function field -/

/-- The Weierstrass relation in the function field `L(E)`: the affine equation for the generic point
`(x, y)`. -/
theorem genY_sq_relation (E : WeierstrassCurve L) :
    (genY E) ^ 2 + algebraMap L (Func E) E.a₁ * genX E * genY E +
        algebraMap L (Func E) E.a₃ * genY E =
      (genX E) ^ 3 + algebraMap L (Func E) E.a₂ * (genX E) ^ 2 +
        algebraMap L (Func E) E.a₄ * genX E + algebraMap L (Func E) E.a₆ := by
  have h := congrArg (algebraMap (Coord E) (Func E)) (coordY_sq_relation E)
  simp only [map_add, map_mul, map_pow] at h
  rw [← IsScalarTower.algebraMap_apply L (Coord E) (Func E) E.a₁,
      ← IsScalarTower.algebraMap_apply L (Coord E) (Func E) E.a₂,
      ← IsScalarTower.algebraMap_apply L (Coord E) (Func E) E.a₃,
      ← IsScalarTower.algebraMap_apply L (Coord E) (Func E) E.a₄,
      ← IsScalarTower.algebraMap_apply L (Coord E) (Func E) E.a₆] at h
  rw [add_mul] at h
  rw [show genX E = (algebraMap (Coord E) (Func E)) (coordX E) from rfl,
      show genY E = (algebraMap (Coord E) (Func E)) (coordY E) from rfl]
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- The generic point of `E` over `L(E)` is a point of the base changed curve: the equation clause
of the first two items, phrased with `WeierstrassCurve.Affine.Equation`. -/
theorem equation_baseE_genX_genY (E : WeierstrassCurve L) :
    WeierstrassCurve.Affine.Equation (baseE E) (genX E) (genY E) := by
  refine (equation_iff (W := baseE E) (genX E) (genY E)).mpr ?_
  simpa only [baseE, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using genY_sq_relation E

/-! ## The Weierstrass relation in the chart at infinity -/

/-- The Weierstrass relation in the chart at infinity, in the coordinates `u = 1/x`, `w = y/x²`:
the equation `w² + a₁uw + a₃u²w = u + a₂u² + a₄u³ + a₆u⁴` obtained from the affine equation by
multiplying by `u⁴`. -/
theorem infW_sq_relation (E : WeierstrassCurve L) :
    (infW E) ^ 2 + algebraMap L (Func E) E.a₁ * infU E * infW E +
        algebraMap L (Func E) E.a₃ * (infU E) ^ 2 * infW E =
      infU E + algebraMap L (Func E) E.a₂ * (infU E) ^ 2 +
        algebraMap L (Func E) E.a₄ * (infU E) ^ 3 +
        algebraMap L (Func E) E.a₆ * (infU E) ^ 4 := by
  have h := genY_sq_relation E
  have hx : genX E ≠ 0 := genX_ne_zero E
  rw [infU, infW]
  field_simp
  linear_combination (norm := first | refl_ring1 | ring1) h

/-! ## Nonsingularity of the rational points -/

/-- On an elliptic curve every point satisfying the Weierstrass equation is nonsingular. -/
theorem nonsingular_of_equation (E : WeierstrassCurve L) [E.IsElliptic] {u v : L}
    (h : WeierstrassCurve.Affine.Equation E u v) :
    WeierstrassCurve.Affine.Nonsingular E u v :=
  (equation_iff_nonsingular (W := E)).mp h

/-! ## The target statement -/

theorem Relations (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic] :
    ((Work.MotC2.coordY E) ^ 2 + (algebraMap L (Work.MotC2.Coord E) E.a₁ * Work.MotC2.coordX E + algebraMap L (Work.MotC2.Coord E) E.a₃) * Work.MotC2.coordY E =
        (Work.MotC2.coordX E) ^ 3 + algebraMap L (Work.MotC2.Coord E) E.a₂ * (Work.MotC2.coordX E) ^ 2 + algebraMap L (Work.MotC2.Coord E) E.a₄ * Work.MotC2.coordX E + algebraMap L (Work.MotC2.Coord E) E.a₆) ∧
      ((Work.MotC2.genY E) ^ 2 + algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E * Work.MotC2.genY E + algebraMap L (Work.MotC2.Func E) E.a₃ * Work.MotC2.genY E =
        (Work.MotC2.genX E) ^ 3 + algebraMap L (Work.MotC2.Func E) E.a₂ * (Work.MotC2.genX E) ^ 2 + algebraMap L (Work.MotC2.Func E) E.a₄ * Work.MotC2.genX E + algebraMap L (Work.MotC2.Func E) E.a₆) ∧
      (WeierstrassCurve.Affine.Equation (Work.MotC2.baseE E) (Work.MotC2.genX E) (Work.MotC2.genY E)) ∧
      ((Work.MotC2.infW E) ^ 2 + algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.infU E * Work.MotC2.infW E + algebraMap L (Work.MotC2.Func E) E.a₃ * (Work.MotC2.infU E) ^ 2 * Work.MotC2.infW E =
        Work.MotC2.infU E + algebraMap L (Work.MotC2.Func E) E.a₂ * (Work.MotC2.infU E) ^ 2 + algebraMap L (Work.MotC2.Func E) E.a₄ * (Work.MotC2.infU E) ^ 3 + algebraMap L (Work.MotC2.Func E) E.a₆ * (Work.MotC2.infU E) ^ 4) ∧
      (∀ u v : L, WeierstrassCurve.Affine.Equation E u v → WeierstrassCurve.Affine.Nonsingular E u v) :=
  ⟨coordY_sq_relation E, genY_sq_relation E, equation_baseE_genX_genY E, infW_sq_relation E,
    fun _ _ h => nonsingular_of_equation E h⟩

end Work.MotC2
