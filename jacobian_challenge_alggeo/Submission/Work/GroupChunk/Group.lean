/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the group chunk `G D` and its class map

From the existence of the glued object (`glued_exists`) this file extracts the concrete
objects of area GC:

* `D.G`, the group chunk;
* `D.chart i`, the chart maps (open immersions);
* `D.cls`, the class map `G(F) → Pic⁰(C_F)`, with `cls_chart`, `cls_bijective` and
  `hom_ext_cls`.
-/
import Submission.Work.GroupChunk.glued_exists

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

/-- The chart datum, as a glued object: the *concrete* gluing of
`Submission/Work/GroupChunk/glued_exists.lean` (so that `D.G` is definitionally the glued
scheme `GSch` of that file, and all of its API is available for the objects below). -/
def toGlued : Glued (C := C) (P0 := P0) where
  G := GSch D
  chart i := chartH D i
  isOpenImmersion i := by
    show IsOpenImmersion (chartH D i).left
    exact isOpenImmersion_ι_glue D i
  factor p := chart_factor (D := D) p
  eq_iff_class i j p q := chart_eq_iff (D := D) i j p q

/-- The group chunk `G D`: the scheme glued from the charts.  It is *definitionally* the
concrete glued scheme `GSch D` of `Submission/Work/GroupChunk/Gluing/Data.lean`, so that all
the API of the gluing datum is available for it without unfolding. -/
abbrev G (D : Input C P0) : Sch K := GSch D

/-- The chart maps `chart i : V ⟶ G D`. -/
abbrev chart (D : Input C P0) (i : D.Idx) : Opens.toOver D.V ⟶ GSch D :=
  chartH D i

/-- The chart maps are open immersions. -/
instance instIsOpenImmersionChart (D : Input C P0) (i : D.Idx) :
    IsOpenImmersion (D.chart i).left :=
  isOpenImmersion_ι_glue D i

/-- The class map `G(F) → Pic⁰(C_F)`. -/
def cls (D : Input C P0) {F : Type u} [Field F] [Algebra K F] (p : FPt D.G F) : Pic0 C F :=
  D.toGlued.cls p

/-- Every field point of `G D` factors through a chart. -/
theorem exists_factor (D : Input C P0) {F : Type u} [Field F] [Algebra K F]
    (p : FPt D.G F) : ∃ (i : D.Idx) (q : FPt (Opens.toOver D.V) F), q ≫ D.chart i = p :=
  D.toGlued.factor p

/-- The class map on a chart is `picOf`. -/
theorem cls_chart (D : Input C P0) {F : Type u} [Field F] [Algebra K F] (i : D.Idx)
    (p : FPt (Opens.toOver D.V) F) :
    D.cls (p ≫ D.chart i) = D.picOf i (p ≫ Opens.ιOver D.V) :=
  D.toGlued.cls_chart i p

/-- Two chart points agree in `G D` exactly when their classes agree. -/
theorem eq_iff_class (D : Input C P0) {F : Type u} [Field F] [Algebra K F] (i j : D.Idx)
    (p q : FPt (Opens.toOver D.V) F) :
    p ≫ D.chart i = q ≫ D.chart j ↔
      D.picOf i (p ≫ Opens.ιOver D.V) = D.picOf j (q ≫ Opens.ιOver D.V) :=
  D.toGlued.eq_iff_class i j p q

/-- The class map is injective. -/
theorem cls_injective (D : Input C P0) {F : Type u} [Field F] [Algebra K F] :
    Function.Injective (D.cls (F := F)) :=
  D.toGlued.cls_injective

/-- The class map is surjective (COV of area CH). -/
theorem cls_surjective (D : Input C P0) {F : Type u} [Field F] [Algebra K F] :
    Function.Surjective (D.cls (F := F)) :=
  D.toGlued.cls_surjective

/-- The class map is a bijection. -/
theorem cls_bijective (D : Input C P0) {F : Type u} [Field F] [Algebra K F] :
    Function.Bijective (D.cls (F := F)) :=
  D.toGlued.cls_bijective

/-- Morphisms into `G D` are detected by their classes at residue-field points. -/
theorem hom_ext_cls (D : Input C P0) [IsSeparated D.G.hom] {Y : Sch K} [IsReduced Y.left]
    (u v : Y ⟶ D.G) (h : ∀ y : Y.left, D.cls (resPt Y y ≫ u) = D.cls (resPt Y y ≫ v)) :
    u = v := by
  haveI : IsSeparated D.toGlued.G.hom := ‹IsSeparated D.G.hom›
  exact D.toGlued.hom_ext_cls u v h

end Input

end

end Work.GroupChunk
