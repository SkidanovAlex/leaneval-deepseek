/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the Abel–Jacobi morphism `AJSym : Sym^g C ⟶ G D`

The Abel–Jacobi morphism (in the form used by the group chunk: `D ↦ [D - g·P0]`) and its
two basic properties: it computes `picAJ` on field points, and it is surjective.
-/
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.AJSym_exists
import Submission.Work.GroupChunk.exists_picAJ_eq

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

namespace Input

variable [D : Input C P0]

/-- **The Abel–Jacobi morphism** `AJSym : Sym^g C ⟶ G D`, the gluing of the chart maps
`ρ i`. -/
def AJSym (D : Input C P0) : D.Sym D.g ⟶ D.G :=
  Classical.choose (AJSym_exists (C := C) (P0 := P0) D.toGlued)

/-- The class of `p ≫ AJSym` is `picAJ p`. -/
theorem cls_AJSym (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (D.Sym D.g) F) :
    D.cls (p ≫ D.AJSym) = D.picAJ p :=
  (Classical.choose_spec (AJSym_exists (C := C) (P0 := P0) D.toGlued)) p

/-- **The Abel–Jacobi morphism is surjective.** -/
theorem AJSym_surjective (D : Input C P0) : Function.Surjective (D.AJSym).left := by
  intro y
  obtain ⟨p, hp⟩ := exists_picAJ_eq (D := D) (F := resField D.G y) (D.cls (resPt D.G y))
  have h : p ≫ D.AJSym = resPt D.G y := by
    apply D.cls_injective (F := resField D.G y)
    rw [cls_AJSym D p, hp]
  refine ⟨p.left (IsLocalRing.closedPoint (resField D.G y)), ?_⟩
  have h2 : p.left ≫ (D.AJSym).left = (resPt D.G y).left := congrArg Over.Hom.left h
  change (p.left ≫ (D.AJSym).left) (IsLocalRing.closedPoint (resField D.G y)) = y
  rw [h2]
  exact resPt_apply D.G y (IsLocalRing.closedPoint (resField D.G y))

end Input

end

end Work.GroupChunk
