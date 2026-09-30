import Mathlib
import Submission.Work.GroupChunk.Gluing.Chart
import Submission.Work.GroupChunk.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GC — existence of the glued group chunk

Assembles the glued object `Work.GroupChunk.Glued C P0` from the concrete gluing datum
`Work.GroupChunk.glueScheme D` of `Submission/Work/GroupChunk/Gluing/Data.lean`, using the two
point-level properties of the gluing proved in `Gluing/Chart.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

theorem glued_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] :
    Nonempty (Work.GroupChunk.Glued (C := C) (P0 := P0)) :=
  ⟨{ G := GSch D
     chart := chartH D
     isOpenImmersion := fun i => by
       show IsOpenImmersion (chartH D i).left
       exact isOpenImmersion_ι_glue D i
     factor := fun p => chart_factor (D := D) p
     eq_iff_class := fun i j p q => chart_eq_iff (D := D) i j p q }⟩

end

end Work.GroupChunk
