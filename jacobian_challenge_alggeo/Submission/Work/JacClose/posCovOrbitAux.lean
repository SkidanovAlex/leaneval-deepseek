/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (the dictionary between `InChart` and `chartRange` for `Inputs`)
-/
import Submission.Work.JacClose.ClosePos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose — the chart/class dictionary for `Work.JacFinal.Inputs`

Two lemmas relating the chart datum of area `GC` (`Work.GroupChunk.Input.InChart`, i.e. "the
class of the point lies in the chart with centre `E i`") to the range of the chart map
`chart i : V ⟶ G'` of area `GC` (`Work.JacFinal.Inputs.chartRange`), for an arbitrary
`k'`-field point and for the canonical `resPt`-point of a point of `G'`:

* `Work.JacClose.inChart_cls_resPt_iff` — `InChart i (cls (resPt G x)) ↔ x ∈ chartRange i`;
* `Work.JacClose.mem_chartRange_of_inChart_fpt` — the forward direction for an arbitrary field
  point (used to turn the `InChart` statement of C6 into the chart-range statement of §1.4(f));
* `Work.JacClose.inChart_of_mem_chartRange` — the backward direction (used to turn §1.4(f) into
  the class-level `Γ`-orbit statement `posCovOrbitProp`).

The forward direction is the argument of `Work.JacFinal.Inputs.mem_chartRange_of_inChart`
(`ChartDict.lean`), read for a general field point; the backward direction uses that an open
immersion has `IsOpenImmersion.lift` along any morphism whose range lands in its range.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.JacClose

noncomputable section

open Work.GCBasics

variable {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
  {P0 : Work.Charts.unitSch k ⟶ C.toOver}

/-- **The forward dictionary, for an arbitrary field point.**  If the class of a `κ`-point `p`
of the glued group chunk is represented in the chart `i`, then the closed point of `p` lies in
the range of the chart map `chart i`. -/
theorem mem_chartRange_of_inChart_fpt (d : Work.JacFinal.Inputs C P0) {F : Type u} [Field F]
    [Algebra d.k' F] (p : FPt d.toChunk.G F) (i : d.chart.Idx)
    (h : d.chart.InChart i (d.exports.glued.cls p)) :
    p.left (IsLocalRing.closedPoint F) ∈ d.chartRange i := by
  haveI : IsOpenImmersion (d.exports.glued.chart i).left := d.exports.glued.isOpenImmersion i
  obtain ⟨y, hy, hc⟩ := h
  obtain ⟨q, hq, -⟩ := FPt.factor_of_landsIn (K := d.k') d.chart.V y hy
  have hcls : d.exports.glued.cls (q ≫ d.exports.glued.chart i) =
      d.exports.glued.cls p := by
    rw [d.exports.glued.cls_chart i q, hq, hc]
  have heq : q ≫ d.exports.glued.chart i = p := d.exports.glued.cls_injective hcls
  rw [Work.JacFinal.Inputs.chartRange, Scheme.Hom.mem_opensRange]
  refine ⟨q.left (IsLocalRing.closedPoint F), ?_⟩
  have hlt : (q.left ≫ (d.exports.glued.chart i).left) = p.left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left heq
  have h2 := congrArg (fun f => f (IsLocalRing.closedPoint F)) hlt
  rw [Scheme.Hom.comp_apply] at h2
  exact h2

/-- **The backward dictionary.**  If a point `x` of the glued group chunk lies in the range of
the chart map `chart i`, then the class of `x` is represented in the chart `i`: the range
membership lifts `resPt G x` along the open immersion `chart i`, and the lift is a point of the
chart, so its class is `cls (resPt G x)`. -/
theorem inChart_of_mem_chartRange (d : Work.JacFinal.Inputs C P0)
    (x : d.toChunk.G.left) (i : d.chart.Idx) (hx : x ∈ d.chartRange i) :
    d.chart.InChart i (d.exports.glued.cls (resPt d.toChunk.G x)) := by
  haveI : IsOpenImmersion (d.exports.glued.chart i).left := d.exports.glued.isOpenImmersion i
  have hx' : x ∈ Scheme.Hom.opensRange (d.exports.glued.chart i).left := hx
  have hmem : Set.range (resPt d.toChunk.G x).left ⊆
      Set.range (d.exports.glued.chart i).left := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [Work.GCBasics.resPt_apply]
    rw [Scheme.Hom.mem_opensRange] at hx'
    exact hx'
  let q : Spec (CommRingCat.of (resField d.toChunk.G x)) ⟶
      (Opens.toOver d.chart.V).left :=
    IsOpenImmersion.lift (d.exports.glued.chart i).left (resPt d.toChunk.G x).left hmem
  have hq : q ≫ (d.exports.glued.chart i).left = (resPt d.toChunk.G x).left :=
    IsOpenImmersion.lift_fac _ _ _
  have hchart : (d.exports.glued.chart i).left ≫ (d.toChunk.G).hom =
      (Opens.toOver d.chart.V).hom := Over.w (d.exports.glued.chart i)
  let qov : FPt (Opens.toOver d.chart.V) (resField d.toChunk.G x) :=
    Over.homMk q (by
      rw [← hchart, ← Category.assoc, hq]
      exact Over.w (resPt d.toChunk.G x))
  have hqov : qov ≫ d.exports.glued.chart i = resPt d.toChunk.G x := by
    apply Over.OverMorphism.ext
    exact hq
  refine ⟨qov ≫ Opens.ιOver d.chart.V, ?_, ?_⟩
  · rw [RPt.landsIn_preimage, Opens.ιOver_left, Scheme.Opens.ι_preimage_self]
    exact RPt.landsIn_top qov
  · rw [← d.exports.glued.cls_chart i qov, hqov]

/-- **The dictionary in `iff` form.**  For a point `x` of the glued group chunk and a chart
index `i`, the class of `x` is in the chart `i` if and only if `x` lies in the range of the
chart map `i`. -/
theorem inChart_cls_resPt_iff (d : Work.JacFinal.Inputs C P0)
    (x : d.toChunk.G.left) (i : d.chart.Idx) :
    d.chart.InChart i (d.exports.glued.cls (resPt d.toChunk.G x)) ↔
      x ∈ d.chartRange i :=
  ⟨fun h => by
      have h' := mem_chartRange_of_inChart_fpt d (resPt d.toChunk.G x) i h
      rwa [Work.GCBasics.resPt_apply] at h',
    fun h => inChart_of_mem_chartRange d x i h⟩

end

end Work.JacClose
