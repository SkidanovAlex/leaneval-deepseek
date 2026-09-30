/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — smoothness of the group chunk `G D`

A group scheme locally of finite type and geometrically reduced over a field is smooth
(`AlgebraicGeometry.smooth_of_grpObj`).  For the group chunk `G D` both hypotheses are
available: `LocallyOfFiniteType` and `GeometricallyReduced` from `Assembly.lean`.
-/
import Mathlib
import Submission.Work.GroupChunk.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.Smooth

universe u
open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem smooth_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [GrpObj (Work.GroupChunk.GSch D)] : Smooth (Work.GroupChunk.GSch D).hom := by
  -- `smooth_of_grpObj` wants the group structure on `Over.mk f`; for the `Over` object
  -- `GSch D` this is definitionally the given group structure.
  have hgrp : GrpObj (Work.GroupChunk.GSch D) := inferInstance
  haveI : GrpObj (Over.mk (Work.GroupChunk.GSch D).hom) :=
    (rfl : Over.mk (Work.GroupChunk.GSch D).hom = Work.GroupChunk.GSch D) ▸ hgrp
  haveI : LocallyOfFiniteType (Work.GroupChunk.GSch D).hom := inferInstance
  haveI : GeometricallyReduced (Work.GroupChunk.GSch D).hom := inferInstance
  exact smooth_of_grpObj (Work.GroupChunk.GSch D).hom

end Work.GroupChunk.Smooth
