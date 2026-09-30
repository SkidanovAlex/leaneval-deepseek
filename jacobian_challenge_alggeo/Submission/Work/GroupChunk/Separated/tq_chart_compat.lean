import Mathlib
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Gluing.Transitions

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

namespace Work.GroupChunk.Separated

universe u
open CategoryTheory in
theorem tq_chart_compat {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) (i j : D.Idx) :
    Work.GroupChunk.tq i j ≫ Work.GroupChunk.chartH D j
      = Work.GCBasics.Opens.ιOver (Work.GroupChunk.U i j) ≫ Work.GroupChunk.chartH D i := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Work.GroupChunk.chartH_left, Work.GCBasics.Opens.ιOver_left]
  rw [← Work.GroupChunk.tr_ιOver i j]
  simp only [Over.comp_left, Work.GCBasics.Opens.ιOver_left]
  exact AlgebraicGeometry.Scheme.GlueData.glue_condition (Work.GroupChunk.glueScheme D) i j

end Work.GroupChunk.Separated
