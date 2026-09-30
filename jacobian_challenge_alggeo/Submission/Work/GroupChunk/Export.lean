/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the exported API of the glued group chunk

`import Submission.Work.GroupChunk.Export` gets the whole of area GC **including** the
downstream-facing statements whose modules import `All` (and therefore cannot be imported by
it): the unconditional `Input.AJ₀_pt` and `Input.AJSym_powMap`.
-/
import Submission.Work.GroupChunk.All
import Submission.Work.GroupChunk.Genus.one_le_g
import Submission.Work.GroupChunk.AJ.AJ0_pt
import Submission.Work.GroupChunk.PowMap.AJSym_powMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

namespace Input

variable [D : Input C P0]

/-- **`AJ₀` sends the base point to the origin.** -/
theorem AJ₀_pt (D : Input C P0) : P0 ≫ Input.AJ₀ D = η[GSch D] :=
  AJ.AJ0_pt D (cls_one_grpObj D)

/-- **`AJSym` is the `g`-fold sum of `AJ₀`** (the lead's `AJSym_quot`). -/
theorem AJSym_powMap (D : Input C P0) {T : Sch K} (x : Fin D.g → (T ⟶ C.toOver)) :
    (D.symGeom D.g).powMap x ≫ D.AJSym = ∏ m, (x m ≫ Input.AJ₀ D) :=
  PowMap.AJSym_powMap D (cls_mul_grpObj D) x

/-- **The class of `AJ₀ x` is `[x] - [P0]`** (`Work.GroupChunk.AJ.cls_AJ0`, under the `Input`
namespace). -/
theorem cls_AJ₀ (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (x : FPt C.toOver F) :
    cls D (x ≫ Input.AJ₀ D) =
      Pic0.mk (SpecLin.ptDiv x - bcKF F D.P0Div)
        (Input.ddeg_ptDiv_sub_bcKF_P0Div (D := D) x) :=
  AJ.cls_AJ0 D x

/-- **The genus of a chart datum is at least one** (`Work.GroupChunk.Genus.one_le_g`, under the
`Input` namespace). -/
theorem one_le_g (D : Input C P0) : 1 ≤ D.g :=
  Genus.one_le_g D

end Input

end

end Work.GroupChunk
