/-
# A finite chart family with metric models, and the structures it produces

This file is the *engine* of the area: a `Work.Space.ModelAtlas` of a topological space `M` is built
from a finite family of charts with metric models, and the two properties that the project consumes
-- that the transitions are isometries of the models (`Work.Space.ModelAtlas.Isometry`) and that
they are smooth (`IsManifold`) -- are *derived* from their pairwise forms.

## The point of the pairwise form

`Work.Space.ModelAtlas.Isometry` is stated with the **priority** chart of a point
(`FinAtlas.indexOf`), which is not locally constant in the atlas of `M̂` (the sources of the charts
of neighbouring pieces accumulate).  It is therefore proved from the pairwise statement

`model j (chart j y) (D a) (D b) = model i (chart i y) a b`

for every pair `i`, `j` and every `y` in the intersection of the two sources, where `D` is the
derivative of the transition `chart j ∘ (chart i)⁻¹` at `(chart i) y`; for `y` near `x` the priority
chart of `x` contains `y` in its (open) source, so the pair of *priority* charts is one of the pairs
covered by the hypothesis.

## Main results

* `Work.RTInstance.PreAtlas.toModelAtlas` — the `ModelAtlas` of the family.
* `Work.RTInstance.PreAtlas.toModelAtlas_isometry` — `Work.Space.ModelAtlas.Isometry` for it.
* `Work.RTInstance.PreAtlas.isManifold` — `IsManifold I4 ∞ M`.
* `Work.RTInstance.PreAtlas.hmodels` — the model curvature datum of
  `Work.Final.FinalInputs.curvLe_field`.

The theorems are stated with the chart-at structure as a *hypothesis* (the identification
`chartAt E4 x = chart (indexOf x)`), so that they can be applied both with the instance derived from
`A.toModelAtlas` and with the one recorded in `Work.Space.RTData`.
-/
import Mathlib
import Submission.Work.RTInstance.Basic

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

/-- **`tangentCoordChange` is the derivative of the transition between the preferred charts.**
For two points of a charted space, the coordinate change of the tangent bundle is the derivative of
the transition `chartAt y ∘ (chartAt x)⁻¹` at `(chartAt x) y`. -/
theorem tangentCoordChange_eq_fderiv {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold I4 1 M] (x y : M) :
    tangentCoordChange I4 x y y =
      fderiv ℝ ((chartAt E4 y : M → E4) ∘ (chartAt E4 x).symm) ((chartAt E4 x) y) := by
  rw [tangentCoordChange_def]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm]
  rw [show (range (id : E4 → E4)) = univ from range_id, fderivWithin_univ]
  rfl

/-- **A finite chart family with metric models.**  The charts are indexed by `Fin n` (so that the
family can be assembled from the fold charts and the filling charts by `Fin.append`); each chart
carries a metric model, and the transitions of the family are smooth and are isometries of the
models, in the pairwise form. -/
structure PreAtlas (M : Type*) [TopologicalSpace M] (n : ℕ) where
  /-- The charts. -/
  chart : Fin n → OpenPartialHomeomorph M E4
  /-- The metric model of each chart, as a family of bilinear forms. -/
  model : Fin n → E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ)
  /-- The models are smooth families of bilinear forms. -/
  model_smooth : ∀ i, ContMDiff 𝓘(ℝ, E4) (𝓘(ℝ, E4).prod 𝓘(ℝ, E4 →L[ℝ] E4 →L[ℝ] ℝ)) ∞
    (fun q : E4 => TotalSpace.mk' (E4 →L[ℝ] E4 →L[ℝ] ℝ) q (model i q))
  /-- The models are symmetric. -/
  model_symm : ∀ i (q v w : E4), model i q v w = model i q w v
  /-- The models are positive definite. -/
  model_pos : ∀ i (q : E4) (v : E4), v ≠ 0 → 0 < model i q v v
  /-- The charts cover the space. -/
  cover : ∀ x : M, ∃ i, x ∈ (chart i).source
  /-- The transitions of the family are smooth. -/
  trans_smooth : ∀ i j : Fin n,
    ContDiffOn ℝ ∞ ((chart j : M → E4) ∘ (chart i).symm) ((chart i).symm ≫ₕ chart j).source
  /-- The transitions are isometries of the models (pairwise form). -/
  trans_iso : ∀ i j : Fin n, ∀ ⦃y : M⦄, y ∈ (chart i).source → y ∈ (chart j).source →
    ∀ a b : E4, model j (chart j y)
        (fderiv ℝ ((chart j : M → E4) ∘ (chart i).symm) ((chart i) y) a)
        (fderiv ℝ ((chart j : M → E4) ∘ (chart i).symm) ((chart i) y) b)
      = model i (chart i y) a b
  /-- The model of a chart has non-positive sectional curvature at the image of a point of its
  source. -/
  model_nonpos : ∀ i : Fin n, ∀ ⦃x : M⦄, x ∈ (chart i).source →
    Curvature.SecNonposAt (fun q a b => model i q a b) (chart i x)

namespace PreAtlas

variable {M : Type*} [TopologicalSpace M] {n : ℕ} (A : PreAtlas M n)

/-- The finite atlas of a `PreAtlas`. -/
@[reducible] def toFinAtlas : Work.Space.FinAtlas M where
  n := n
  chart := A.chart
  cover := A.cover

/-- The model atlas of a `PreAtlas`. -/
@[reducible] def toModelAtlas : Work.Space.ModelAtlas M where
  toFinAtlas := A.toFinAtlas
  model := A.model
  model_smooth := A.model_smooth
  model_symm := A.model_symm
  model_pos := A.model_pos

/-- The metric field of the `i`-th chart, in the vocabulary of `Work.Curvature`. -/
def field (i : Fin n) : Curvature.MetricField := fun q a b => A.model i q a b

theorem field_apply (i : Fin n) (q a b : E4) : A.field i q a b = A.model i q a b := rfl

/-- **The transitions of the family are isometries of the models, in the form of
`Work.Space.ModelAtlas.Isometry`.**  The hypothesis `hchart` says that the preferred chart of the
ambient charted space structure is the priority chart of the family. -/
theorem toModelAtlas_isometry [ChartedSpace E4 M] [IsManifold I4 1 M]
    (hchart : ∀ x, (chartAt E4 x : OpenPartialHomeomorph M E4) =
      A.chart (Work.Space.FinAtlas.indexOf A.toFinAtlas x)) :
    A.toModelAtlas.Isometry := by
  intro x
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ (A.chart (Work.Space.FinAtlas.indexOf A.toFinAtlas x)).source :=
    (A.chart _).open_source.mem_nhds (Work.Space.FinAtlas.indexOf_mem A.toFinAtlas x)
  filter_upwards [hsrc] with y hy a b
  have hcx : (chartAt E4 x : M → E4) = ⇑(A.chart (Work.Space.FinAtlas.indexOf A.toFinAtlas x)) :=
    congrArg (fun e : OpenPartialHomeomorph M E4 => (⇑e)) (hchart x)
  have hcy : (chartAt E4 y : M → E4) = ⇑(A.chart (Work.Space.FinAtlas.indexOf A.toFinAtlas y)) :=
    congrArg (fun e : OpenPartialHomeomorph M E4 => (⇑e)) (hchart y)
  have hsy : ((chartAt E4 x).symm : E4 → M) =
      ⇑((A.chart (Work.Space.FinAtlas.indexOf A.toFinAtlas x)).symm) :=
    congrArg (fun e : OpenPartialHomeomorph M E4 => (⇑(e.symm))) (hchart x)
  rw [tangentCoordChange_eq_fderiv]
  rw [hcx, hcy, hsy]
  exact A.trans_iso _ _ hy (Work.Space.FinAtlas.indexOf_mem A.toFinAtlas y) a b

/-- **The transitions of the finite family are smooth**, whence `IsManifold I4 ∞ M`. -/
theorem isManifold (A : PreAtlas M n) :
    letI : Work.Space.FinAtlas M := A.toFinAtlas
    IsManifold I4 ∞ M :=
  Work.Space.isManifold_of_contDiffOn_transitions_infty (A := A.toFinAtlas) A.trans_smooth

end PreAtlas

/-- **The `Work.Space.RTData` of an assembly with a chart family.**  This is the single datum that
`Work.Final.FinalInputs` still owes: the assembled space `M̂` with its finite atlas of isometric
models.  The isometry and the smoothness of the transitions are the theorems proved above. -/
@[instance_reducible] noncomputable def toRTData {n : ℕ} (a : Work.Space.Assembly) (A : PreAtlas a.Mhat n) :
    Work.Space.RTData where
  core := a
  models := A.toModelAtlas
  manifold := by
    letI : Work.Space.FinAtlas a.Mhat := A.toFinAtlas
    exact A.isManifold
  isometry := by
    letI : Work.Space.FinAtlas a.Mhat := A.toFinAtlas
    letI hM : IsManifold I4 ∞ a.Mhat := A.isManifold
    haveI : IsManifold I4 1 a.Mhat := inferInstance
    exact A.toModelAtlas_isometry (hchart := fun x => rfl)
  transition_smooth := A.trans_smooth

end Work.RTInstance
