/-
# The fold block of the atlas from the charts of the area `FoldInst`

The area `FoldInst` has delivered the 98 fold charts of `M̄`:

* `Work.FoldInst.foldChart : Fin 98 → OpenPartialHomeomorph Mbar E4`,
* `Work.FoldInst.foldChart_source` (the source is the union of the images of the Voronoi pieces),
* `Work.FoldInst.foldChart_source_subset_compl_Tset` (the sources avoid the cusped boundary),
* `Work.FoldInst.iUnion_foldChart_source` / `mem_foldChart_source` (they cover `M̄ ∖ Tset`).

This file shows that the fold block `Work.RTInstance.FoldData` of the atlas is *exactly* that data
together with three analytic facts: that the transitions of the charts are smooth
(`FoldAnalytic.smooth`) and are isometries of the upper half space model (`FoldAnalytic.iso`), and
that the chart images have height `> δ` (`FoldAnalytic.ok`).  Hence a provider of `FillData` and
`CrossData` (the area `Cusp`, and the interface statement) gets the instance

`(Work.RTInstance.owedOf g A G C).toRTData : Work.Space.RTData`.

Mathematically, the two analytic facts follow from the chart formula
`foldChart i (mk x) = foldTheta i r x.2.1` (`Work.FoldInst.foldChart_apply`): `foldTheta` is
`coordPerm ∘ mobiusKlein (N_F D_r)`, so a transition is `coordPerm_j ∘ mobius (A_j A_i⁻¹) ∘
coordPerm_i⁻¹`, a composition of Möbius maps with a permutation of the first three coordinates (the
height is fixed), hence smooth (`HypModel.mobius_contDiffOn`) and an isometry of the upper half space
metric (`HypModel.mobius_isometry`, `uhsMetric` being invariant under permutations of the first three
coordinates).  The height condition follows from the compactness of `Q̄` and `Q̄ ⊆` the ball: the
height is a continuous positive function on `Q̄`, so it is bounded below by some `δ > 0`.
-/
import Mathlib
import Submission.Work.RTInstance.Instance
import Submission.Work.FoldInst.FoldChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace
open Bundle

namespace Work.RTInstance

/-- **The three analytic facts about the fold charts of `FoldInst`** that the atlas needs. -/
structure FoldAnalytic where
  /-- The height margin of the fold chart images. -/
  δ : ℝ
  /-- The margin is positive. -/
  hδ : 0 < δ
  /-- The transitions of the fold charts are smooth. -/
  smooth : ∀ i j : Fin 98,
    ContDiffOn ℝ ∞
      ((Work.FoldInst.foldChart j : Work.FoldInst.Mbar → E4) ∘
        (Work.FoldInst.foldChart i).symm)
      ((Work.FoldInst.foldChart i).symm ≫ₕ Work.FoldInst.foldChart j).source
  /-- The transitions of the fold charts are isometries of the upper half space model. -/
  iso : ∀ i j : Fin 98, ∀ ⦃y : Work.FoldInst.Mbar⦄,
    y ∈ (Work.FoldInst.foldChart i).source → y ∈ (Work.FoldInst.foldChart j).source →
    ∀ u v : E4,
      uhsModel δ (Work.FoldInst.foldChart j y)
        (fderiv ℝ ((Work.FoldInst.foldChart j : Work.FoldInst.Mbar → E4) ∘
          (Work.FoldInst.foldChart i).symm) ((Work.FoldInst.foldChart i) y) u)
        (fderiv ℝ ((Work.FoldInst.foldChart j : Work.FoldInst.Mbar → E4) ∘
          (Work.FoldInst.foldChart i).symm) ((Work.FoldInst.foldChart i) y) v)
      = uhsModel δ (Work.FoldInst.foldChart i y) u v
  /-- The images of the fold charts have height `> δ`. -/
  ok : ∀ i : Fin 98, ∀ ⦃y : Work.FoldInst.Mbar⦄,
    y ∈ (Work.FoldInst.foldChart i).source → (ChartLayer.uhs δ).ok (Work.FoldInst.foldChart i y)

/-- **The fold block of the atlas, from the delivered fold charts of `FoldInst`.** -/
noncomputable def FoldAnalytic.toFoldData (g : GlueHomeo) (A : FoldAnalytic) :
    FoldData (assemblyOf g) where
  δ := A.δ
  hδ := A.hδ
  nF := 98
  foldChart := Work.FoldInst.foldChart
  fold_source := fun i => Work.FoldInst.foldChart_source_subset_compl_Tset i
  fold_cover := fun x hx => Work.FoldInst.mem_foldChart_source hx
  fold_smooth := A.smooth
  fold_iso := A.iso
  fold_ok := A.ok

/-- **The pending inputs of the atlas of `M̂`**, with the fold block taken from the delivered charts
of `FoldInst`: what is owed is the three analytic facts of `FoldAnalytic`, the charts of the filling
side (`FillData`, the deliverable of `Cusp`) and the cross transitions (`CrossData`). -/
noncomputable def owedOf (g : GlueHomeo) (A : FoldAnalytic) (G : FillData (assemblyOf g))
    (C : CrossData (assemblyOf g) (A.toFoldData g) G) : Owed (assemblyOf g) :=
  ⟨A.toFoldData g, G, C⟩

end Work.RTInstance
