/-
# The curvature datum `Work.CurvModels.ModelCurvature` of the atlas of `M̂`

The area `CurvModels` computes the curvature of `M̂` from a datum `ModelCurvature A` on the atlas
`A`: for each chart, which of the documented metric models it carries (`kind`), that the atlas model
*is* that metric on the chart target (`eq_model`), and that the target lies in the region of the
model (`target_subset`).  This file registers that datum for the atlas produced by
`Work.RTInstance.Owed`:

* the fold charts carry `Work.CurvModels.ModelData.uhs` (their targets have height `> δ`, a field of
  `FoldData`);
* the filling charts carry the model of their layer `ChartLayer` — `ModelData.uhs` for the collar
  charts, `ModelData.warped P` for the polar charts of a profile, `ModelData.flat h₀` for the core
  charts.  `eq_model` is the agreement of the total models `uhsModel`/`warpedModelA` with the
  geometric metrics `Work.Curvature.uhsMetric`/`warpedMetric` on the targets (`uhsModel_eq_uhsMetric`,
  `warpedModelA_eq_warpedMetric`, `flatModel_eq_flatMetric`), and `target_subset` is the `ok`
  condition of the layer at the chart image (`FoldData.fold_ok`, `FillData.fill_ok`).

Consequently `Work.CurvModels.hmodels` gives the model curvature datum of
`Work.Final.FinalInputs.curvLe_field` for this instance
(`Work.RTInstance.Owed.hmodels_of_modelCurvature`).
-/
import Mathlib
import Submission.Work.RTInstance.Instance
import Submission.Work.CurvModels.ModelCurvature
import Submission.Work.CurvModels.Hmodels

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

namespace ChartLayer

/-- **The `Work.CurvModels.ModelData` of a chart layer**: the documented model which the (total)
model of the layer modifies. -/
def data (l : ChartLayer) (hl : l.okAnywhere) : Work.CurvModels.ModelData :=
  match hl' : l with
  | uhs _ => Work.CurvModels.ModelData.uhs
  | warped P => Work.CurvModels.ModelData.warped P
  | flat h₀ => Work.CurvModels.ModelData.flat h₀ (by
      have h : (ChartLayer.flat h₀).okAnywhere := hl' ▸ hl
      exact h)

@[simp] theorem data_uhs (δ : ℝ) (hl : (uhs δ).okAnywhere) :
    (uhs δ).data hl = Work.CurvModels.ModelData.uhs := rfl

@[simp] theorem data_warped (P : Work.Profiles.FillProfile) (hl : (warped P).okAnywhere) :
    (warped P).data hl = Work.CurvModels.ModelData.warped P := rfl

@[simp] theorem data_flat (h₀ : ℝ) (hl : (flat h₀).okAnywhere) :
    (flat h₀).data hl = Work.CurvModels.ModelData.flat h₀ hl := rfl

/-- **The model of a layer is the metric of its model datum** on the region of the layer
(the total models `uhsModel`/`warpedModelA`/`flatModel` agree with the geometric metrics there). -/
theorem model_eq_data (l : ChartLayer) (hl : l.okAnywhere) {q : E4} (hq : l.ok q) (u v : E4) :
    l.model q u v = (l.data hl).metric q u v := by
  cases l with
  | uhs δ =>
      change 0 < δ ∧ δ < q 3 at hq
      change uhsModel δ q u v = Curvature.uhsMetric q u v
      exact uhsModel_eq_uhsMetric hq.1 (le_of_lt hq.2) u v
  | warped P =>
      change (1/4 : ℝ) < q 0 at hq
      change warpedModelA P.f P.h q u v = Curvature.warpedMetric P.f P.h q u v
      exact warpedModelA_eq_warpedMetric (le_of_lt (lt_trans (by norm_num) hq)) u v
  | flat h₀ =>
      change flatModel h₀ q u v = Curvature.flatMetric h₀ q u v
      exact flatModel_eq_flatMetric h₀ q u v

/-- **The region of a layer is contained in the region of its model datum.** -/
theorem ok_subset_region (l : ChartLayer) (hl : l.okAnywhere) :
    {q : E4 | l.ok q} ⊆ (l.data hl).region := by
  intro q hq
  cases l with
  | uhs δ =>
      change 0 < δ ∧ δ < q 3 at hq
      change (0 : ℝ) < q 3
      exact lt_trans hq.1 hq.2
  | warped P =>
      change (1/4 : ℝ) < q 0 at hq
      change (0 : ℝ) < q 0
      exact lt_trans (by norm_num) hq
  | flat h₀ =>
      change q ∈ (Set.univ : Set E4)
      exact Set.mem_univ q

end ChartLayer

namespace Owed

variable {a : Work.Space.Assembly} (h : Owed a)

/-- **The model datum of each chart of the atlas**: `ModelData.uhs` on the fold block, and the data
of its layer on the filling block. -/
def kindM : Fin (h.F.nF + h.G.nC) → Work.CurvModels.ModelData :=
  Fin.append (fun _ => Work.CurvModels.ModelData.uhs)
    (fun j => ChartLayer.data (h.G.fillLayer j) (h.G.fill_anywhere j))

@[simp] theorem kindM_castAdd (i : Fin h.F.nF) :
    kindM h (Fin.castAdd h.G.nC i) = Work.CurvModels.ModelData.uhs :=
  Fin.append_left _ _ i

@[simp] theorem kindM_natAdd (j : Fin h.G.nC) :
    kindM h (Fin.natAdd h.F.nF j) =
      ChartLayer.data (h.G.fillLayer j) (h.G.fill_anywhere j) :=
  Fin.append_right _ _ j

/-- The image of a point of the source of a fold chart has height `> δ` (so the total model
`uhsModel δ` is the upper half space metric there). -/
theorem fold_image_ok (i : Fin h.F.nF) ⦃x : a.Mhat⦄ (hx : x ∈ (h.F.foldM i).source) :
    h.F.δ < ((h.F.foldM i) x) 3 := by
  have hx' : x ∈ a.incMbar '' (h.F.foldChart i).source := by rwa [FoldData.foldM_source h.F i] at hx
  obtain ⟨y, hy, rfl⟩ := hx'
  rw [FoldData.foldM_apply h.F i hy]
  exact (h.F.fold_ok i hy).2

/-- **The target of a transported fold chart lies in `{δ < q 3}`.** -/
theorem fold_target_ok (i : Fin h.F.nF) {q : E4} (hq : q ∈ (h.F.foldM i).target) :
    h.F.δ < q 3 := by
  have hmem : (h.F.foldM i).symm q ∈ (h.F.foldM i).source := (h.F.foldM i).map_target hq
  have hval : (h.F.foldM i) ((h.F.foldM i).symm q) = q := (h.F.foldM i).right_inv hq
  have h3 := h.fold_image_ok i hmem
  rwa [hval] at h3

/-- The image of a point of the source of a filling chart lies in the region of its layer. -/
theorem fill_image_ok (j : Fin h.G.nC) ⦃x : a.Mhat⦄ (hx : x ∈ (h.G.fillChart j).source) :
    (h.G.fillLayer j).ok ((h.G.fillChart j) x) :=
  h.G.fill_ok j hx

/-- **The target of a filling chart lies in the region of its layer.** -/
theorem fill_target_ok (j : Fin h.G.nC) {q : E4} (hq : q ∈ (h.G.fillChart j).target) :
    (h.G.fillLayer j).ok q := by
  have hmem : (h.G.fillChart j).symm q ∈ (h.G.fillChart j).source := (h.G.fillChart j).map_target hq
  have hval : (h.G.fillChart j) ((h.G.fillChart j).symm q) = q := (h.G.fillChart j).right_inv hq
  rw [← hval]
  exact h.fill_image_ok j hmem

/-- **The curvature datum of the atlas of `M̂`**, in the form `CurvModels` consumes. -/
noncomputable def modelCurvature : Work.CurvModels.ModelCurvature h.preAtlas.toModelAtlas where
  kind := h.kindM
  eq_model := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · -- a fold chart
      intro q hq u v
      change q ∈ (h.chartM (Fin.castAdd h.G.nC i')).target at hq
      rw [chartM_castAdd h i'] at hq
      change h.modelM (Fin.castAdd h.G.nC i') q u v
        = (h.kindM (Fin.castAdd h.G.nC i')).metric q u v
      rw [modelM_castAdd h i', kindM_castAdd h i']
      change uhsModel h.F.δ q u v = Curvature.uhsMetric q u v
      exact uhsModel_eq_uhsMetric h.F.hδ (le_of_lt (h.fold_target_ok i' hq)) u v
    · -- a filling chart
      intro q hq u v
      change q ∈ (h.chartM (Fin.natAdd h.F.nF j)).target at hq
      rw [chartM_natAdd h j] at hq
      change h.modelM (Fin.natAdd h.F.nF j) q u v
        = (h.kindM (Fin.natAdd h.F.nF j)).metric q u v
      rw [modelM_natAdd h j, kindM_natAdd h j]
      exact ChartLayer.model_eq_data (h.G.fillLayer j) (h.G.fill_anywhere j)
        (h.fill_target_ok j hq) u v
  target_subset := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · change (h.chartM (Fin.castAdd h.G.nC i')).target ⊆
        (h.kindM (Fin.castAdd h.G.nC i')).region
      rw [chartM_castAdd h i', kindM_castAdd h i']
      change (h.F.foldM i').target ⊆ Work.CurvModels.ModelData.uhs.region
      intro q hq
      change (0 : ℝ) < q 3
      exact lt_trans h.F.hδ (h.fold_target_ok i' hq)
    · change (h.chartM (Fin.natAdd h.F.nF j)).target ⊆ (h.kindM (Fin.natAdd h.F.nF j)).region
      rw [chartM_natAdd h j, kindM_natAdd h j]
      intro q hq
      exact ChartLayer.ok_subset_region (h.G.fillLayer j) (h.G.fill_anywhere j)
        (h.fill_target_ok j hq)

/-- **The curvature datum of `Work.Final.FinalInputs.curvLe_field`** for the instance of `M̂`,
through the `CurvModels` route. -/
theorem hmodels_of_modelCurvature :
    ∀ x : h.toRTData.Mhat, ∃ G ∈ h.toRTData.models.models,
      Curvature.SecNonposAt G ((extChartAt I4 x) x) ∧
      ∀ᶠ q in 𝓝 ((extChartAt I4 x) x), ∀ a b : E4,
        Submission.ChartConnection.chartGram (I := I4) x ((extChartAt I4 x).symm q) a b
          = G q a b := by
  haveI : Work.CurvModels.ModelCurvature h.toRTData.models := h.modelCurvature
  exact Work.CurvModels.hmodels (rt := h.toRTData)

end Owed

end Work.RTInstance
