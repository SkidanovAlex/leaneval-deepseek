/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GenusZero.Basic
import Submission.Work.KeyLemma.Sum
import Submission.Work.SpecLin.Points.ptDiv_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: the divisor of a point has degree one

The genus-zero argument (`Const.lean`) needs that the divisor `[x]` of a `k`-point of a curve
has degree one, so that `[x] - [y]` has degree zero and falls under
`Work.GenusZero.principal_of_deg_zero`.

For a `k`-point `p` of `C` the closed point `placeOfPoint C p` is the image of a section of the
structure morphism `C.hom` (a `k`-point is a section, and a curve is proper, hence separated),
so its residue degree is one (`Work.SpecLin.Points.residueDegree_of_section`).  Hence

  `deg [p] = deg (Finsupp.single (placeOfPoint C p) 1) = 1 · [κ(Q) : k] = 1`.

## Main results

* `Work.GenusZero.residueDegree_placeOfPoint`
* `Work.GenusZero.toDiv_single_one`
* `Work.GenusZero.deg_toDiv_single_one`
-/

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.GenusZero

variable {k : Type u} [Field k]

/-- The closed point attached to a `k`-point of a curve is the image of the underlying
morphism of schemes at the (unique) point of `Spec k`. -/
theorem placeOfPoint_point (C : CurveBasics.Curve k) (p : KeyLemma.Curve.Point C) :
    (KeyLemma.Curve.placeOfPoint C p).point =
      KeyLemma.Curve.Pt.leftHom p (IsLocalRing.closedPoint k) := rfl

/-- The residue degree of the closed point attached to a `k`-point is one. -/
theorem residueDegree_placeOfPoint (C : CurveBasics.Curve k)
    (p : KeyLemma.Curve.Point C) :
    C.hom.residueDegree (KeyLemma.Curve.placeOfPoint C p).point = 1 := by
  rw [placeOfPoint_point]
  exact Work.SpecLin.Points.residueDegree_of_section (KeyLemma.Curve.Pt.leftHom p) C.hom
    (KeyLemma.Curve.Pt.leftHom_comp p) (IsLocalRing.closedPoint k)

/-- The divisor of a simple `k`-point of a curve is the place attached to it. -/
theorem toDiv_single_one (C : CurveBasics.Curve k) (p : KeyLemma.Curve.Point C) :
    KeyLemma.Curve.SumDiv.toDiv C (Finsupp.single p 1) =
      CurveBasics.Curve.Div.place (KeyLemma.Curve.placeOfPoint C p) := by
  rw [KeyLemma.Curve.SumDiv.toDiv, Finsupp.sum_single_index (by simp)]
  rfl

/-- The divisor `[p]` of a `k`-point of a curve has degree one. -/
@[simp]
theorem deg_toDiv_single_one (C : CurveBasics.Curve k) (p : KeyLemma.Curve.Point C) :
    C.deg (KeyLemma.Curve.SumDiv.toDiv C (Finsupp.single p 1)) = 1 := by
  rw [toDiv_single_one, CurveBasics.Curve.deg_place, residueDegree_placeOfPoint, Nat.cast_one]

end Work.GenusZero
