/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area CurveFacts
-/
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveFacts.SmoothReduced
import Submission.Work.CurveFacts.krullDimLE_stalk_of_smoothOfRelativeDimension_one
import Submission.Work.CurveFacts.nontrivial_of_smoothOfRelativeDimension_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Area `CurveFacts`: the three hypotheses of `Work.CurveBasics.Curve.ofOver` are now theorems

`Work.CurveBasics.Curve` bundles, next to the three hypotheses of the Jacobian challenge
(smooth of relative dimension one, proper, geometrically irreducible), the three facts about
curves that were not available when that structure was introduced:

* `geomReduced : GeometricallyReduced C.hom` (item A1),
* `krullDim_stalk_le_one : ∀ z, Ring.KrullDimLE 1 (stalk z)` (item A2),
* `nontrivial : Nontrivial C.left` (item A3).

Items A1–A3 of this area prove all three from the challenge's hypotheses, so the extra arguments
of `Curve.ofOver` can be filled in.  The convenience constructor below does exactly that, so that
nothing downstream has to reach past the interface of this area.
-/
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace Work.CurveFacts

/-- **A curve in the sense of the Jacobian challenge is a curve.**  Given the hypotheses of the
challenge (`SmoothOfRelativeDimension 1`, `IsProper`, `GeometricallyIrreducible`) and a nonempty
underlying space, build `Work.CurveBasics.Curve k` using items A1, A2 and A3 of area `CurveFacts`
for the three fields that `Work.CurveBasics.ofOver` asks for separately. -/
noncomputable def curveOfOver {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (hne : Nonempty C.left) : Work.CurveBasics.Curve k :=
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  Work.CurveBasics.Curve.ofOver C
    (geometricallyReduced_of_smooth C.hom)
    (fun z => krullDimLE_stalk_of_smoothOfRelativeDimension_one C.hom z)
    (by haveI := hne; exact nontrivial_of_smoothOfRelativeDimension_one C.hom)

/-- The underlying scheme of `Work.CurveFacts.curveOfOver` is the given one. -/
@[simp]
theorem curveOfOver_toOver {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (hne : Nonempty C.left) : (curveOfOver C hne).toOver = C := rfl

end Work.CurveFacts
