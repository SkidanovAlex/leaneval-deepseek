/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — `G D` is smooth over `K`

A geometrically reduced group scheme of finite type over a field is smooth
(`AlgebraicGeometry.smooth_of_grpObj`).  With the group structure of
`Submission/Work/GroupChunk/GroupLaw/Basic.lean` this makes `Smooth (G D).hom` an instance.
-/
import Submission.Work.GroupChunk.GroupLaw.Basic
import Submission.Work.GroupChunk.Smooth.smooth_G

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-- `G D` is smooth over `K`. -/
instance instSmooth_G (D : Input C P0) : Smooth (GSch D).hom :=
  Smooth.smooth_G D

end

end Work.GroupChunk
