/-
# The concrete instance `Work.Space.RTData` of `M̂`

This file produces the one field that `Work.Final.FinalInputs` still owes: the datum
`rt : Work.Space.RTData` of the assembled space `M̂` of the Ratcliffe--Tschantz construction.

## The two blocks of the atlas

* the **fold charts** of the hyperbolic piece `M̄`: `nF` charts of `M̄` avoiding the cusped boundary
  `Tset`, transported to `M̂` by `Work.RTInstance.exists_chartOfMbar` (this is the deliverable of the
  area `FoldInst`, whose `exists_foldChart` gives exactly such charts), with the model `uhsModel δ`;
* the **filling charts** on `M̂` (the collar/cusp charts crossing the gluing, and the polar and core
  charts of the filling pieces) with their layers `ChartLayer` (this is the deliverable of the area
  `Cusp`).

The pending inputs of those two areas are the fields of the structure `Owed` below, stated *in the
vocabulary of this area* (so that they are discharged by citing `exists_foldChart`, the cover
theorem `fold_cover_sides`, the cusp charts `Work.Cusp.exists_cuspChart`/`exists_polarChartS`/
`exists_coreChart` and the isometry theorems of `HypModel`).

## What is proved here

Given the pending inputs, this file

* builds the finite chart family of `M̂` (`PreAtlas`), with
  * the models of `ChartLayer` (smooth, symmetric, positive definite, non-positively curved at the
    chart images: `Models.lean`, `LayerPos.lean`, `ChartLayer_secNonposAt`),
  * the cover (`Owed.cover`, from the fold cover of `M̄ ∖ Tset` and the filling cover),
  * the smoothness and the isometry of the transitions (same-block cases from the pending data,
    cross cases from the pending data of the interface),
* and hence the instance `Work.RTInstance.rtData : Work.Space.RTData` by the engine
  `Work.RTInstance.toRTData`.

The model curvature datum of `Work.Final.FinalInputs.curvLe_field` follows:
`Work.RTInstance.RTDataNonpos.hmodels`.
-/
import Mathlib
import Submission.Work.RTInstance.PreAtlas
import Submission.Work.RTInstance.LayerPos
import Submission.Work.RTInstance.exists_chartOfMbar
import Submission.Work.RTInstance.model_smooth
import Submission.Work.RTInstance.Models
import Submission.Work.RTInstance.uhsModel_pos
import Submission.Work.RTInstance.warpedModelA_pos
import Submission.Work.RTInstance.flatModel_pos
import Submission.Work.RTInstance.posExt_pos
import Submission.Work.RTInstance.CurvDatum
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.Connected

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

/-! ### The assembly of `M̂` from the gluing homeomorphism -/

/-- **The gluing of the filling pieces to the hyperbolic piece** (the `τ_v` identification of the
area `Cusp`): the cusped boundary `Tset` of `M̄` is homeomorphic to the boundary
`∂[-1,1]² × T_v` of the five filling pieces. -/
structure GlueHomeo where
  /-- The gluing homeomorphism. -/
  glue : Work.FoldInst.Tset ≃ₜ
    {q : Σ _ : Work.Space.Cusp, SquarePt × Torus //
      q ∈ Work.Space.FillingBdry (fun _ : Work.Space.Cusp => Torus)}

/-- **The topological assembly of `M̂`**: the hyperbolic piece `M̄` of `FoldInst`, the five filling
pieces `[-1,1]² × T_v` with `T_v = (ℝ/ℤ)²`, and the gluing.  Its `Mhat` is the space `M̂`. -/
def assemblyOf (g : GlueHomeo) : Work.Space.Assembly where
  Mbar := Work.FoldInst.Mbar
  Torus := fun _ => Torus
  Tset := Work.FoldInst.Tset
  Tset_closed := Work.FoldInst.isClosed_Tset
  glue := g.glue

/-! ### The pending inputs of `FOLDINST` and `CUSP` -/

/-- **The charts of the hyperbolic side, on `M̄`.**  This is the deliverable of the area `FoldInst`:
`exists_foldChart` produces, for each of the `98` fold classes, a chart of `M̄` whose source is the
union of the images of the Voronoi pieces and whose value on `mk x` is `foldTheta`.  All the fields
below are facts about those charts that the area knows (the smoothness and isometry of the
transitions are the `mobius_isometry`/`mobius_contDiffOn` of `HypModel` applied to the chart
formula; the cover is the area's `Cover.lean`). -/
structure FoldData (a : Work.Space.Assembly) where
  /-- The margin of the upper half space model: every fold chart image has height `> δ`. -/
  δ : ℝ
  /-- The margin is positive. -/
  hδ : 0 < δ
  /-- The number of fold charts (the `98` classes of the RT data). -/
  nF : ℕ
  /-- The fold charts of `M̄`. -/
  foldChart : Fin nF → OpenPartialHomeomorph a.Mbar E4
  /-- Their sources avoid the cusped boundary. -/
  fold_source : ∀ i : Fin nF, (foldChart i).source ⊆ a.Tsetᶜ
  /-- They cover `M̄ ∖ Tset`. -/
  fold_cover : ∀ x : a.Mbar, x ∉ a.Tset → ∃ i : Fin nF, x ∈ (foldChart i).source
  /-- The transitions of the fold charts are smooth. -/
  fold_smooth : ∀ i j : Fin nF,
    ContDiffOn ℝ ∞ ((foldChart j : a.Mbar → E4) ∘ (foldChart i).symm)
      ((foldChart i).symm ≫ₕ foldChart j).source
  /-- The transitions of the fold charts are isometries of the upper half space model. -/
  fold_iso : ∀ i j : Fin nF, ∀ ⦃y : a.Mbar⦄, y ∈ (foldChart i).source →
    y ∈ (foldChart j).source → ∀ u v : E4,
      uhsModel δ (foldChart j y)
        (fderiv ℝ ((foldChart j : a.Mbar → E4) ∘ (foldChart i).symm) ((foldChart i) y) u)
        (fderiv ℝ ((foldChart j : a.Mbar → E4) ∘ (foldChart i).symm) ((foldChart i) y) v)
      = uhsModel δ (foldChart i y) u v
  /-- **The height condition**: the image of a point of the source of a fold chart has height
  `> δ`, so that the total model `uhsModel δ` agrees with the upper half space metric there. -/
  fold_ok : ∀ i : Fin nF, ∀ ⦃y : a.Mbar⦄, y ∈ (foldChart i).source →
    (ChartLayer.uhs δ).ok (foldChart i y)

/-- **The charts of the filling side, on `M̂`.**  This is the deliverable of the area `Cusp`: the
collar charts (which cross the gluing along the cusped boundary and are the charts of the UHS model
in the collar), the polar charts of the filling pieces (`ChartLayer.warped P` for the profile `P` of
the cusp) and the core charts (`ChartLayer.flat h₀`). -/
structure FillData (a : Work.Space.Assembly) where
  /-- The number of filling charts. -/
  nC : ℕ
  /-- The filling charts of `M̂`. -/
  fillChart : Fin nC → OpenPartialHomeomorph a.Mhat E4
  /-- The metric layer of each filling chart. -/
  fillLayer : Fin nC → ChartLayer
  /-- The global non-degeneracy input of each layer (positivity of the model). -/
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
  /-- **The layer condition at the chart images**: the image of a point of the source of a filling
  chart lies in the region where its layer is non-positively curved. -/
  fill_ok : ∀ j : Fin nC, ∀ ⦃x : a.Mhat⦄, x ∈ (fillChart j).source →
    (fillLayer j).ok (fillChart j x)
  /-- The filling charts cover the complement of the image of `M̄ ∖ Tset`. -/
  fill_cover : ∀ x : a.Mhat, (∀ p : a.Mbar, p ∉ a.Tset → a.incMbar p ≠ x) →
    ∃ j : Fin nC, x ∈ (fillChart j).source

namespace FoldData

variable {a : Work.Space.Assembly} (F : FoldData a)

/-- **The fold chart of `M̄` as a chart of `M̂`**: the transport of `F.foldChart i` along the open
embedding `M̄ ∖ Tset → M̂`. -/
noncomputable def foldM (i : Fin F.nF) : OpenPartialHomeomorph a.Mhat E4 :=
  (exists_chartOfMbar a (F.foldChart i) (F.fold_source i)).choose

theorem foldM_source (i : Fin F.nF) :
    (foldM F i).source = a.incMbar '' (F.foldChart i).source :=
  (exists_chartOfMbar a (F.foldChart i) (F.fold_source i)).choose_spec.1

theorem foldM_target (i : Fin F.nF) : (foldM F i).target = (F.foldChart i).target :=
  (exists_chartOfMbar a (F.foldChart i) (F.fold_source i)).choose_spec.2.1

theorem foldM_apply (i : Fin F.nF) {x : a.Mbar} (hx : x ∈ (F.foldChart i).source) :
    foldM F i (a.incMbar x) = F.foldChart i x :=
  (exists_chartOfMbar a (F.foldChart i) (F.fold_source i)).choose_spec.2.2.1 x hx

theorem foldM_symm (i : Fin F.nF) {q : E4} (hq : q ∈ (foldM F i).target) :
    (foldM F i).symm q = a.incMbar ((F.foldChart i).symm q) :=
  (exists_chartOfMbar a (F.foldChart i) (F.fold_source i)).choose_spec.2.2.2 q hq

/-- **The transition of two transported fold charts is the transition of the charts of `M̄`.** -/
theorem foldM_trans (i j : Fin F.nF) {q : E4}
    (hq : q ∈ ((foldM F i).symm ≫ₕ foldM F j).source) :
    foldM F j ((foldM F i).symm q) = F.foldChart j ((F.foldChart i).symm q) := by
  have hq1 : q ∈ (foldM F i).target := hq.1
  have hsym : (foldM F i).symm q = a.incMbar ((F.foldChart i).symm q) := foldM_symm F i hq1
  have hmem : a.incMbar ((F.foldChart i).symm q) ∈ (foldM F j).source := hsym ▸ hq.2
  rw [foldM_source F j] at hmem
  obtain ⟨z, hz, hzq⟩ := hmem
  have hzy : z = (F.foldChart i).symm q := a.incMbar_injective hzq
  have hy : (F.foldChart i).symm q ∈ (F.foldChart j).source := hzy ▸ hz
  rw [hsym, foldM_apply F j hy]

/-- The trans source of two transported fold charts is the trans source of the charts of `M̄`. -/
theorem foldM_trans_source (i j : Fin F.nF) :
    ((foldM F i).symm ≫ₕ foldM F j).source = ((F.foldChart i).symm ≫ₕ F.foldChart j).source := by
  ext q
  constructor
  · rintro ⟨hq1, hq2⟩
    have hq2' : (foldM F i).symm q ∈ (foldM F j).source := hq2
    have h1 : q ∈ (F.foldChart i).target := by
      rw [← foldM_target F i]; exact hq1
    refine ⟨h1, ?_⟩
    have h2 : a.incMbar ((F.foldChart i).symm q) ∈ (foldM F j).source :=
      (foldM_symm F i hq1) ▸ hq2'
    rw [foldM_source F j] at h2
    obtain ⟨z, hz, hzq⟩ := h2
    have hzy : z = (F.foldChart i).symm q := a.incMbar_injective hzq
    rwa [hzy] at hz
  · rintro ⟨hq1, hq2⟩
    have h1 : q ∈ (foldM F i).target := by
      rw [foldM_target F i]; exact hq1
    refine ⟨h1, ?_⟩
    show (foldM F i).symm q ∈ (foldM F j).source
    rw [foldM_symm F i h1, foldM_source F j]
    exact ⟨(F.foldChart i).symm q, hq2, rfl⟩

/-- **The smoothness of the transition of two transported fold charts.** -/
theorem foldM_smooth (i j : Fin F.nF) :
    ContDiffOn ℝ ∞ ((foldM F j : a.Mhat → E4) ∘ (foldM F i).symm)
      ((foldM F i).symm ≫ₕ foldM F j).source := by
  have h1 : ContDiffOn ℝ ∞ ((F.foldChart j : a.Mbar → E4) ∘ (F.foldChart i).symm)
      ((foldM F i).symm ≫ₕ foldM F j).source :=
    (F.fold_smooth i j).mono (fun q hq => (foldM_trans_source F i j) ▸ hq)
  exact h1.congr (fun q hq => foldM_trans F i j hq)

/-- **The derivative of the transition of two transported fold charts is the derivative of the
transition of the charts of `M̄`.** -/
theorem foldM_fderiv (i j : Fin F.nF) {y' : a.Mbar} (hi : y' ∈ (F.foldChart i).source)
    (hj : y' ∈ (F.foldChart j).source) :
    fderiv ℝ ((F.foldM j : a.Mhat → E4) ∘ (F.foldM i).symm) ((F.foldM i) (a.incMbar y'))
      = fderiv ℝ ((F.foldChart j : a.Mbar → E4) ∘ (F.foldChart i).symm)
          ((F.foldChart i) y') := by
  have hpt : (F.foldM i) (a.incMbar y') = (F.foldChart i) y' := foldM_apply F i hi
  rw [hpt]
  refine Filter.EventuallyEq.fderiv_eq ?_
  have htarget : (F.foldChart i) y' ∈ (F.foldM i).target := by
    rw [foldM_target F i]; exact (F.foldChart i).map_source hi
  have hsrc : (F.foldM i).symm ((F.foldChart i) y') ∈ (F.foldM j).source := by
    rw [foldM_symm F i htarget, (F.foldChart i).left_inv hi, foldM_source F j]
    exact ⟨y', hj, rfl⟩
  have hmem : (F.foldChart i) y' ∈ ((F.foldM i).symm ≫ₕ F.foldM j).source := ⟨htarget, hsrc⟩
  filter_upwards [IsOpen.mem_nhds (((F.foldM i).symm ≫ₕ F.foldM j)).open_source hmem] with q hq
  exact foldM_trans F i j hq

/-- **The transition of two transported fold charts is an isometry of the upper half space
model** (from the corresponding statement on `M̄`). -/
theorem foldM_iso (i j : Fin F.nF) ⦃y : a.Mhat⦄ (hyi : y ∈ (foldM F i).source)
    (hyj : y ∈ (foldM F j).source) (u v : E4) :
    uhsModel F.δ (foldM F j y)
      (fderiv ℝ ((foldM F j : a.Mhat → E4) ∘ (foldM F i).symm) ((foldM F i) y) u)
      (fderiv ℝ ((foldM F j : a.Mhat → E4) ∘ (foldM F i).symm) ((foldM F i) y) v)
    = uhsModel F.δ (foldM F i y) u v := by
  have hyi' : y ∈ a.incMbar '' (F.foldChart i).source := by rwa [foldM_source F i] at hyi
  have hyj' : y ∈ a.incMbar '' (F.foldChart j).source := by rwa [foldM_source F j] at hyj
  obtain ⟨y', hi, hyeq⟩ := hyi'
  obtain ⟨z, hz, hzq⟩ := hyj'
  have hzy : z = y' := a.incMbar_injective (by rw [hzq, hyeq])
  have hj : y' ∈ (F.foldChart j).source := hzy ▸ hz
  rw [← hyeq, foldM_fderiv F i j hi hj, foldM_apply F i hi, foldM_apply F j hj]
  exact F.fold_iso i j hi hj u v

end FoldData

/-- **The cross transitions of the atlas**: the transitions between a transported fold chart and a
filling chart.  This is the part of the geometry of `M̂` that belongs to the interface of the two
areas: near the cusped boundary the collar chart of `Cusp` and the fold chart of `FoldInst` describe
the same hyperbolic metric, so their transition is an isometry of the upper half space model.

The four fields are the two directions of smoothness and of the isometry, in the pairwise form that
`Work.RTInstance.PreAtlas` consumes. -/
structure CrossData (a : Work.Space.Assembly) (F : FoldData a) (G : FillData a) where
  /-- The transition fill ∘ fold⁻¹ is smooth. -/
  cross_smooth_fg : ∀ (i : Fin F.nF) (j : Fin G.nC),
    ContDiffOn ℝ ∞ ((G.fillChart j : a.Mhat → E4) ∘ (F.foldM i).symm)
      ((F.foldM i).symm ≫ₕ G.fillChart j).source
  /-- The transition fold ∘ fill⁻¹ is smooth. -/
  cross_smooth_gf : ∀ (i : Fin F.nF) (j : Fin G.nC),
    ContDiffOn ℝ ∞ ((F.foldM i : a.Mhat → E4) ∘ (G.fillChart j).symm)
      ((G.fillChart j).symm ≫ₕ F.foldM i).source
  /-- The transition fill ∘ fold⁻¹ is an isometry of the models. -/
  cross_iso_fg : ∀ (i : Fin F.nF) (j : Fin G.nC), ∀ ⦃y : a.Mhat⦄, y ∈ (F.foldM i).source →
    y ∈ (G.fillChart j).source → ∀ u v : E4,
      (G.fillLayer j).model (G.fillChart j y)
        (fderiv ℝ ((G.fillChart j : a.Mhat → E4) ∘ (F.foldM i).symm) ((F.foldM i) y) u)
        (fderiv ℝ ((G.fillChart j : a.Mhat → E4) ∘ (F.foldM i).symm) ((F.foldM i) y) v)
      = uhsModel F.δ ((F.foldM i) y) u v
  /-- The transition fold ∘ fill⁻¹ is an isometry of the models. -/
  cross_iso_gf : ∀ (i : Fin F.nF) (j : Fin G.nC), ∀ ⦃y : a.Mhat⦄, y ∈ (G.fillChart j).source →
    y ∈ (F.foldM i).source → ∀ u v : E4,
      uhsModel F.δ ((F.foldM i) y)
        (fderiv ℝ ((F.foldM i : a.Mhat → E4) ∘ (G.fillChart j).symm) ((G.fillChart j) y) u)
        (fderiv ℝ ((F.foldM i : a.Mhat → E4) ∘ (G.fillChart j).symm) ((G.fillChart j) y) v)
      = (G.fillLayer j).model (G.fillChart j y) u v

/-- **The pending inputs of the two areas, bundled.** -/
structure Owed (a : Work.Space.Assembly) where
  /-- The fold charts of the hyperbolic side. -/
  F : FoldData a
  /-- The filling charts. -/
  G : FillData a
  /-- The cross transitions. -/
  cross : CrossData a F G

namespace Owed

variable {a : Work.Space.Assembly} (h : Owed a)

/-- The combined chart family of `M̂`: the transported fold charts, then the filling charts. -/
noncomputable def chartM : Fin (h.F.nF + h.G.nC) → OpenPartialHomeomorph a.Mhat E4 :=
  Fin.append (fun i => h.F.foldM i) h.G.fillChart

/-- The combined model family: the upper half space model on the fold block, the layer models on
the filling block. -/
def modelM : Fin (h.F.nF + h.G.nC) → E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ) :=
  Fin.append (fun _ => uhsModel h.F.δ) (fun j => (h.G.fillLayer j).model)

/-- The layer of each chart of the combined family. -/
def layerM : Fin (h.F.nF + h.G.nC) → ChartLayer :=
  Fin.append (fun _ => ChartLayer.uhs h.F.δ) h.G.fillLayer

@[simp] theorem chartM_castAdd (i : Fin h.F.nF) :
    chartM h (Fin.castAdd h.G.nC i) = h.F.foldM i :=
  Fin.append_left _ _ i

@[simp] theorem chartM_natAdd (j : Fin h.G.nC) :
    chartM h (Fin.natAdd h.F.nF j) = h.G.fillChart j :=
  Fin.append_right _ _ j

@[simp] theorem modelM_castAdd (i : Fin h.F.nF) :
    modelM h (Fin.castAdd h.G.nC i) = uhsModel h.F.δ :=
  Fin.append_left _ _ i

@[simp] theorem modelM_natAdd (j : Fin h.G.nC) :
    modelM h (Fin.natAdd h.F.nF j) = (h.G.fillLayer j).model :=
  Fin.append_right _ _ j

@[simp] theorem layerM_castAdd (i : Fin h.F.nF) :
    layerM h (Fin.castAdd h.G.nC i) = ChartLayer.uhs h.F.δ :=
  Fin.append_left _ _ i

@[simp] theorem layerM_natAdd (j : Fin h.G.nC) :
    layerM h (Fin.natAdd h.F.nF j) = h.G.fillLayer j :=
  Fin.append_right _ _ j

theorem layerM_okAnywhere (i : Fin (h.F.nF + h.G.nC)) : (layerM h i).okAnywhere := by
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · rw [layerM_castAdd]; exact h.F.hδ
  · rw [layerM_natAdd]; exact h.G.fill_anywhere j

/-- The cover of the combined chart family: `M̄ ∖ Tset` by the fold charts, the rest by the filling
charts. -/
theorem coverM (x : a.Mhat) : ∃ i : Fin (h.F.nF + h.G.nC), x ∈ (chartM h i).source := by
  by_cases hx : ∃ p : a.Mbar, p ∉ a.Tset ∧ a.incMbar p = x
  · obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨i, hi⟩ := h.F.fold_cover p hp
    refine ⟨Fin.castAdd h.G.nC i, ?_⟩
    rw [chartM_castAdd, FoldData.foldM_source]
    exact ⟨p, hi, hpx⟩
  · obtain ⟨j, hj⟩ := h.G.fill_cover x (fun p hp hpx => hx ⟨p, hp, hpx⟩)
    exact ⟨Fin.natAdd h.F.nF j, by rw [chartM_natAdd]; exact hj⟩

/-- **The pairwise smoothness of the transitions of the atlas.** -/
theorem trans_smoothM : ∀ i j : Fin (h.F.nF + h.G.nC),
    ContDiffOn ℝ ∞ ((chartM h j : a.Mhat → E4) ∘ (chartM h i).symm)
      ((chartM h i).symm ≫ₕ chartM h j).source := by
  intro i j
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
  · refine Fin.addCases (fun i'' => ?_) (fun j'' => ?_) j
    · simpa only [chartM_castAdd] using h.F.foldM_smooth i' i''
    · simpa only [chartM_castAdd, chartM_natAdd] using h.cross.cross_smooth_fg i' j''
  · refine Fin.addCases (fun i'' => ?_) (fun j'' => ?_) j
    · simpa only [chartM_natAdd, chartM_castAdd] using h.cross.cross_smooth_gf i'' j'
    · simpa only [chartM_natAdd] using h.G.fill_smooth j' j''

/-- **The pairwise isometry of the transitions of the atlas.** -/
theorem trans_isoM : ∀ i j : Fin (h.F.nF + h.G.nC), ∀ ⦃y : a.Mhat⦄,
    y ∈ (chartM h i).source → y ∈ (chartM h j).source → ∀ u v : E4,
      modelM h j (chartM h j y)
        (fderiv ℝ ((chartM h j : a.Mhat → E4) ∘ (chartM h i).symm) ((chartM h i) y) u)
        (fderiv ℝ ((chartM h j : a.Mhat → E4) ∘ (chartM h i).symm) ((chartM h i) y) v)
      = modelM h i (chartM h i y) u v := by
  intro i j
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
  · refine Fin.addCases (fun i'' => ?_) (fun j'' => ?_) j
    · intro y hyi hyj u v
      have hyi' : y ∈ (h.F.foldM i').source := by simpa only [chartM_castAdd] using hyi
      have hyj' : y ∈ (h.F.foldM i'').source := by simpa only [chartM_castAdd] using hyj
      rw [modelM_castAdd h, modelM_castAdd h, chartM_castAdd h, chartM_castAdd h]
      exact h.F.foldM_iso i' i'' hyi' hyj' u v
    · intro y hyi hyj u v
      have hyi' : y ∈ (h.F.foldM i').source := by simpa only [chartM_castAdd] using hyi
      have hyj' : y ∈ (h.G.fillChart j'').source := by simpa only [chartM_natAdd] using hyj
      rw [modelM_castAdd h, modelM_natAdd h, chartM_castAdd h, chartM_natAdd h]
      exact h.cross.cross_iso_fg i' j'' hyi' hyj' u v
  · refine Fin.addCases (fun i'' => ?_) (fun j'' => ?_) j
    · intro y hyi hyj u v
      have hyi' : y ∈ (h.G.fillChart j').source := by simpa only [chartM_natAdd] using hyi
      have hyj' : y ∈ (h.F.foldM i'').source := by simpa only [chartM_castAdd] using hyj
      rw [modelM_castAdd h, modelM_natAdd h, chartM_castAdd h, chartM_natAdd h]
      exact h.cross.cross_iso_gf i'' j' hyi' hyj' u v
    · intro y hyi hyj u v
      have hyi' : y ∈ (h.G.fillChart j').source := by simpa only [chartM_natAdd] using hyi
      have hyj' : y ∈ (h.G.fillChart j'').source := by simpa only [chartM_natAdd] using hyj
      rw [modelM_natAdd h, modelM_natAdd h, chartM_natAdd h, chartM_natAdd h]
      exact h.G.fill_iso j' j'' hyi' hyj' u v

/-- **The pairwise non-positivity of the models of the atlas at the chart images.** -/
theorem model_nonposM : ∀ i : Fin (h.F.nF + h.G.nC), ∀ ⦃x : a.Mhat⦄,
    x ∈ (chartM h i).source → Curvature.SecNonposAt (fun q a b => modelM h i q a b)
      (chartM h i x) := by
  intro i
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · intro x hx
    have hx' : x ∈ (h.F.foldM i').source := by simpa only [chartM_castAdd] using hx
    have hx'' : x ∈ a.incMbar '' (h.F.foldChart i').source := by
      rwa [FoldData.foldM_source h.F i'] at hx'
    obtain ⟨y', hy', rfl⟩ := hx''
    rw [modelM_castAdd h, chartM_castAdd h, FoldData.foldM_apply h.F i' hy']
    exact ChartLayer.secNonposAt (ChartLayer.uhs h.F.δ) (h.F.fold_ok i' hy')
  · intro x hx
    have hx' : x ∈ (h.G.fillChart j).source := by simpa only [chartM_natAdd] using hx
    rw [modelM_natAdd h, chartM_natAdd h]
    exact ChartLayer.secNonposAt (h.G.fillLayer j) (h.G.fill_ok j hx')

/-- **The chart family of the assembled space `M̂`**: the fold charts (transported from `M̄`) and
the filling charts, with the models of their layers. -/
noncomputable def preAtlas (h : Owed a) : PreAtlas a.Mhat (h.F.nF + h.G.nC) where
  chart := h.chartM
  model := h.modelM
  model_smooth := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · rw [modelM_castAdd h]; exact model_smooth (ChartLayer.uhs h.F.δ)
    · rw [modelM_natAdd h]; exact model_smooth (h.G.fillLayer j)
  model_symm := by
    intro i q u v
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · rw [modelM_castAdd h]; exact ChartLayer.model_symm (ChartLayer.uhs h.F.δ) q u v
    · rw [modelM_natAdd h]; exact ChartLayer.model_symm (h.G.fillLayer j) q u v
  model_pos := by
    intro i q v hv
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · rw [modelM_castAdd h]; exact uhsModel_pos h.F.δ h.F.hδ q v hv
    · rw [modelM_natAdd h]
      exact ChartLayer_model_pos_of (h.G.fillLayer j) (h.G.fill_anywhere j) q v hv
  cover := h.coverM
  trans_smooth := h.trans_smoothM
  trans_iso := h.trans_isoM
  model_nonpos := h.model_nonposM

/-- **The instance `Work.Space.RTData` of `M̂`**, modulo the pending inputs of the areas `FoldInst`
and `Cusp`.  This is the field `rt` of `Work.Final.FinalInputs`. -/
noncomputable def toRTData (h : Owed a) : Work.Space.RTData :=
  RTInstance.toRTData a h.preAtlas

/-- **The curvature datum of `Work.Final.FinalInputs.curvLe_field` for this instance.** -/
theorem toRTData_nonpos (h : Owed a) : RTDataNonpos h.toRTData :=
  ⟨fun i x hx => h.model_nonposM i hx⟩

end Owed

end Work.RTInstance
