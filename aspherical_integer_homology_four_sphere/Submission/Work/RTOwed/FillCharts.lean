/-
# Item 2, reduced: the filling charts and their layer covers give `FillData`

`Work.RTInstance.FillData a` is the bundle of the filling charts of `M̂`: the chart family with its
metric layers, the layer conditions at the chart images, the smoothness and isometry of the
transitions, and the **cover** of the part of `M̂` that does not come from the open hyperbolic piece
`M̄ ∖ Tset`.

The cover is not independent data: it follows from the *layer* covers (the collar layer
`‖p‖∞ ≥ 1/2`, the inner polar layer `1/24 < ‖p‖∞ < 1/2` and the core layer `‖p‖∞ < 1/12` of the five
filling pieces), which is exactly the form in which the area `Cusp` proves it
(`Work.Cusp.fill_cover_of_layer_cover`, on top of `Work.Cusp.cover_univ` and the pointwise layer
inclusions `Work.Cusp.collarLayer_subset_range_cuspCoordMTop`,
`Work.Cusp.polarLayer_subset_range_polarCoordM`, `Work.Cusp.coreLayer_subset_range_coreCoordM`).

This file performs that reduction: `Work.RTOwed.FillCharts` is `FillData` with `fill_cover` replaced
by the three layer covers, and `Work.RTOwed.FillCharts.toFillData` produces the `FillData`, so that a
caller never has to prove the cover of `M̂` by hand.
-/
import Mathlib
import Submission.Work.RTInstance.Instance
import Submission.Work.Cusp.cover_univ_charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace Matrix

namespace Work.RTOwed

open Work.RTInstance

/-- **The filling charts of `M̂` with the three layer covers** (item 2 of the contract, with the
cover obligation expressed on the layers, which is the form in which the area `Cusp` delivers it).

Every field is a field of `Work.RTInstance.FillData` except `collar_cover`, `polar_cover`,
`core_cover`, which replace the single field `fill_cover`; `Work.RTOwed.FillCharts.toFillData`
proves the cover of `M̂` from them by `Work.Cusp.fill_cover_of_layer_cover`. -/
structure FillCharts (a : Work.Space.Assembly) where
  /-- The number of filling charts. -/
  nC : ℕ
  /-- The filling charts of `M̂` (the collar charts crossing the gluing, the polar charts and the
  core charts of the five filling pieces, assembled from `Work.Cusp.cuspChart`,
  `Work.Cusp.polarChart`, `Work.Cusp.coreChart`). -/
  fillChart : Fin nC → OpenPartialHomeomorph a.Mhat E4
  /-- The metric layer of each filling chart (`ChartLayer.uhs δ` in the collar,
  `ChartLayer.warped P` in the polar annulus, `ChartLayer.flat h₀` in the core). -/
  fillLayer : Fin nC → ChartLayer
  /-- The global non-degeneracy input of each layer. -/
  fill_anywhere : ∀ j : Fin nC, (fillLayer j).okAnywhere
  /-- The transitions of the filling charts are smooth. -/
  fill_smooth : ∀ i j : Fin nC,
    ContDiffOn ℝ ∞ ((fillChart j : a.Mhat → E4) ∘ (fillChart i).symm)
      ((fillChart i).symm ≫ₕ fillChart j).source
  /-- The transitions of the filling charts are isometries of their layers. -/
  fill_iso : ∀ i j : Fin nC, ∀ ⦃y : a.Mhat⦄, y ∈ (fillChart i).source →
    y ∈ (fillChart j).source → ∀ u v : E4,
      (fillLayer j).model (fillChart j y)
        (fderiv ℝ ((fillChart j : a.Mhat → E4) ∘ (fillChart i).symm) ((fillChart i) y) u)
        (fderiv ℝ ((fillChart j : a.Mhat → E4) ∘ (fillChart i).symm) ((fillChart i) y) v)
      = (fillLayer i).model (fillChart i y) u v
  /-- The layer condition at the chart images. -/
  fill_ok : ∀ j : Fin nC, ∀ ⦃x : a.Mhat⦄, x ∈ (fillChart j).source →
    (fillLayer j).ok (fillChart j x)
  /-- **The collar cover**: every point of the collar layer `‖p‖∞ ≥ 1/2` of every filling piece
  lies in the source of one of the filling charts (for the concrete family: the collar charts
  `Work.Cusp.cuspChart`, cf. `Work.Cusp.collarLayer_subset_range_cuspCoordMTop`). -/
  collar_cover : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
    q ∈ Work.Cusp.collarLayer (a.Torus v) → ∃ j, a.incW v q ∈ (fillChart j).source
  /-- **The polar cover**: every point of the inner polar layer `1/24 < ‖p‖∞ < 1/2` lies in the
  source of one of the filling charts (for the concrete family: the polar charts
  `Work.Cusp.polarChart`, cf. `Work.Cusp.polarLayer_subset_range_polarCoordM`). -/
  polar_cover : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
    q ∈ Work.Cusp.polarLayer (a.Torus v) → Work.Cusp.nrm (q.1 : Work.Cusp.E2) < 1/2 →
      ∃ j, a.incW v q ∈ (fillChart j).source
  /-- **The core cover**: every point of the core layer `‖p‖∞ < 1/12` lies in the source of one of
  the filling charts (for the concrete family: the core charts `Work.Cusp.coreChart`, cf.
  `Work.Cusp.coreLayer_subset_range_coreCoordM`). -/
  core_cover : ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
    q ∈ Work.Cusp.coreLayer (a.Torus v) → ∃ j, a.incW v q ∈ (fillChart j).source

namespace FillCharts

variable {a : Work.Space.Assembly}

/-- **The cover of the filling charts of `M̂`**, from the three layer covers and from the cover of
the open hyperbolic piece by the fold charts.  This is the field `fill_cover` of
`Work.RTInstance.FillData`; it is *proved* here, not assumed. -/
theorem fill_cover (F : FoldData a) (G : FillCharts a) :
    ∀ x : a.Mhat, (∀ p : a.Mbar, p ∉ a.Tset → a.incMbar p ≠ x) →
      ∃ j : Fin G.nC, x ∈ (G.fillChart j).source :=
  Work.Cusp.fill_cover_of_layer_cover a (Fin F.nF) (fun i => F.foldChart i)
    (fun x hx => Set.mem_iUnion.mpr (F.fold_cover x hx)) (fun i => F.fold_source i) G.nC G.fillChart G.collar_cover G.polar_cover G.core_cover

/-- **Item 2 of the contract from the layer covers**: the filling charts and their transition data,
together with the layer covers, produce the `FillData` of `M̂`. -/
def toFillData (G : FillCharts a) (F : FoldData a) : FillData a where
  nC := G.nC
  fillChart := G.fillChart
  fillLayer := G.fillLayer
  fill_anywhere := G.fill_anywhere
  fill_smooth := G.fill_smooth
  fill_iso := G.fill_iso
  fill_ok := G.fill_ok
  fill_cover := G.fill_cover F

end FillCharts

end Work.RTOwed
