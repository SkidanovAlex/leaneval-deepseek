/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area CurveFacts
-/
import Submission.Work.AbVar.SmoothReduced.geometricallyReduced_of_smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area `CurveFacts`, item **A1**: a scheme smooth over a field is (geometrically) reduced

This file exports, under the names requested by the closure design
(`Submission/Work/NOTES_LEAD_jacobian_closure.md` §2.A, A1), the two statements

* `Work.CurveFacts.isReduced_of_smooth` — a scheme smooth over `Spec K` for a field `K` is
  reduced;
* `Work.CurveFacts.geometricallyReduced_of_smooth` — a morphism of schemes which is smooth is
  geometrically reduced.

These are the inputs `hred : GeometricallyReduced C.hom` of `Work.CurveBasics.Curve.ofOver`
(the hypothesis `hred` of item O1 of the closure design).

The mathematics — a smooth algebra over a field is reduced, via the local structure theorem
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` and
`Algebra.FormallyUnramified.isReduced_of_field` — is proved in area `AbVar`
(`Work.AbVar.SmoothReduced.isGeometricallyReduced_of_smooth` and
`Work.AbVar.SmoothReduced.geometricallyReduced_of_smooth`).  Nothing here is new mathematics;
the file exists so that area `CurveFacts` has the interface at its own names.
-/
set_option autoImplicit false

universe u

namespace Work.CurveFacts

open CategoryTheory AlgebraicGeometry

/-- **A scheme smooth over the spectrum of a field is reduced.** -/
theorem isReduced_of_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] : IsReduced X :=
  Work.AbVar.SmoothReduced.isReduced_of_smoothOverSpecField f

/-- **A smooth morphism of schemes is geometrically reduced.**  This is `hred` of the closure
design: for the structure morphism `C ⟶ Spec k` of a smooth curve it produces
`GeometricallyReduced C.hom`. -/
theorem geometricallyReduced_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : GeometricallyReduced f :=
  Work.AbVar.SmoothReduced.geometricallyReduced_of_smooth f

end Work.CurveFacts
