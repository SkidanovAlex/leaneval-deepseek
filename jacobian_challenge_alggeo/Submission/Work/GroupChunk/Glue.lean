/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the glued group chunk `G D`

The group chunk `G D` is obtained by gluing copies of the chart `V ⊆ Sym^g C` along the
transition morphisms `t i j`.  This file records the *interface* through which the rest of
the area uses the gluing:

* `G : Sch K`, the glued scheme;
* `chart i : Opens.toOver D.V ⟶ G`, the chart maps (open immersions);
* every field point of `G` factors through a chart;
* two chart points have the same image in `G` **iff** they have the same divisor class
  (`picOf`).

The last property is the mathematical content of the gluing: one direction is the fact that
the transitions preserve classes (`t_cls`), the other the KEY lemma `landsIn_U_iff` together
with the description of `t` as `σ`.
-/
import Submission.Work.GroupChunk.AbelJacobi

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

section

variable [D : Input C P0]

/-- The data of the glued group chunk: a `K`-scheme `G` with chart maps from `V`, such that the
points of `G` are exactly the classes of degree zero on `C`. -/
structure Glued where
  /-- the glued scheme. -/
  G : Sch K
  /-- the chart maps. -/
  chart : ∀ i : D.Idx, Opens.toOver D.V ⟶ G
  /-- the chart maps are open immersions. -/
  isOpenImmersion : ∀ i : D.Idx, IsOpenImmersion (chart i).left
  /-- every field point of `G` factors through a chart. -/
  factor : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt G F),
    ∃ (i : D.Idx) (q : FPt (Opens.toOver D.V) F), q ≫ chart i = p
  /-- two chart points agree in `G` exactly when their classes agree. -/
  eq_iff_class : ∀ {F : Type u} [Field F] [Algebra K F] (i j : D.Idx)
    (p q : FPt (Opens.toOver D.V) F),
    p ≫ chart i = q ≫ chart j ↔
      D.picOf i (p ≫ Opens.ιOver D.V) = D.picOf j (q ≫ Opens.ιOver D.V)

namespace Glued

variable (X : Glued (C := C) (P0 := P0))

/-- The class map `G(F) → Pic⁰(C_F)`: factor a point through a chart and take its class. -/
def cls {F : Type u} [Field F] [Algebra K F] (p : FPt X.G F) : Pic0 C F :=
  D.picOf (X.factor p).choose ((X.factor p).choose_spec.choose ≫ Opens.ιOver D.V)

/-- The class map on the `i`-th chart is `picOf i`. -/
theorem cls_chart {F : Type u} [Field F] [Algebra K F] (i : D.Idx)
    (p : FPt (Opens.toOver D.V) F) :
    X.cls (D := D) (p ≫ X.chart i) = D.picOf i (p ≫ Opens.ιOver D.V) :=
  (X.eq_iff_class _ _ _ _).mp (X.factor (p ≫ X.chart i)).choose_spec.choose_spec

/-- The class map is the same on any chart through which a point factors. -/
theorem cls_eq_picOf {F : Type u} [Field F] [Algebra K F] {p : FPt X.G F}
    {i : D.Idx} {q : FPt (Opens.toOver D.V) F} (hq : q ≫ X.chart i = p) :
    X.cls (D := D) p = D.picOf i (q ≫ Opens.ιOver D.V) := by
  have h := (X.factor p).choose_spec.choose_spec
  have h2 : (X.factor p).choose_spec.choose ≫ X.chart (X.factor p).choose = q ≫ X.chart i := by
    rw [h, hq]
  exact (X.eq_iff_class _ _ _ _).mp h2

/-- The class map is injective. -/
theorem cls_injective {F : Type u} [Field F] [Algebra K F] :
    Function.Injective (X.cls (D := D) (F := F)) := by
  intro p q hpq
  obtain ⟨i, p', hp'⟩ := X.factor p
  obtain ⟨j, q', hq'⟩ := X.factor q
  have hcls : D.picOf i (p' ≫ Opens.ιOver D.V) = D.picOf j (q' ≫ Opens.ιOver D.V) := by
    rw [← X.cls_eq_picOf hp', ← X.cls_eq_picOf hq']
    exact hpq
  rw [← hp', ← hq']
  exact (X.eq_iff_class i j p' q').mpr hcls

/-- The class map is surjective (COV of area CH). -/
theorem cls_surjective {F : Type u} [Field F] [Algebra K F] :
    Function.Surjective (X.cls (D := D) (F := F)) := by
  intro c
  obtain ⟨i, y, hy, hc⟩ := D.cov c
  obtain ⟨y', hy', -⟩ := FPt.factor_of_landsIn (K := K) D.V y hy
  refine ⟨y' ≫ X.chart i, ?_⟩
  rw [X.cls_chart i y', hy']
  exact hc

/-- The class map is a bijection. -/
theorem cls_bijective {F : Type u} [Field F] [Algebra K F] :
    Function.Bijective (X.cls (D := D) (F := F)) :=
  ⟨X.cls_injective, X.cls_surjective⟩

/-- Morphisms into `G` are detected by their classes at residue-field points. -/
theorem hom_ext_cls [IsSeparated X.G.hom] {Y : Sch K} [IsReduced Y.left] (u v : Y ⟶ X.G)
    (h : ∀ y : Y.left,
      X.cls (D := D) (resPt Y y ≫ u) = X.cls (D := D) (resPt Y y ≫ v)) :
    u = v :=
  hom_ext_of_resPt (X := Y) (Y := X.G) u v fun y => X.cls_injective (D := D) (h y)

end Glued

end

end

end Work.GroupChunk
