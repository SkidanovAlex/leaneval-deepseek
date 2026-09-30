/-
# The model curvature datum of `M̂` (the `hmodels` of the final assembly)

Area `Submission/Work/CurvModels/`.  This file contains the deliverable of the area: for the
assembled manifold `M̂` (`Work.Space.RTData`), the datum that the final assembly
(`Work.Final.FinalInputs`, see `Submission/Work/Final/NOTES_FINAL.md` §5) expects,

```
∀ x : M̂, ∃ G ∈ rt.models.models,
    SecNonposAt G (chart x) ∧ ∀ᶠ q in 𝓝 (chart x), ∀ a b, chartGram x (chart⁻¹ q) a b = G q a b
```

from the atlas curvature datum `Work.CurvModels.ModelCurvature` of `Hmodels.lean`'s sibling
`ModelCurvature.lean`:

* the model is the atlas field `rt.models.field (rt.models.indexOf x)` of the preferred chart of
  `x` — this is what makes the pointwise case split of `ModelCurvature.secNonposAt_field_of_mem`
  apply, since `(extChartAt I4 x) x = (A.chart (A.indexOf x)) x`;
* that field belongs to `rt.models.models = Set.range rt.models.field`;
* the sign of the sectional curvature is the per-point case split;
* the eventual agreement with `chartGram` is `Work.CurvModels.chartGram_eventually_field`.

There is also `hmodels_of_chartSec`: the same datum from the *direct* per-chart hypothesis, for a
provider who has already proved the sign fact on each chart target (and does not want to go through
`ModelCurvature`).

`Work.CurvModels.curvLe_of_models` (`FinalBridge.lean`) feeds this datum to
`Work.Final.curvLe_of_models` and returns the `curvLe` field itself.
-/
import Mathlib
import Submission.Work.CurvModels.ModelCurvature
import Submission.Work.CurvModels.chartGram_eventually_field

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Filter Topology
open scoped Manifold ContDiff Bundle Topology
open Work.Curvature

namespace Work.CurvModels

/-- The image of `x` in the ext-chart at `x` is the image of `x` in its preferred atlas chart. -/
theorem extChartAt_self_eq_chart {M : Type*} [TopologicalSpace M] [A : Work.Space.ModelAtlas M]
    (x : M) :
    (extChartAt Work.Space.I4 x) x = (A.chart (A.indexOf x)) x := by
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply]
  rfl

/-- **The model curvature datum of `M̂`** — the `hmodels` of `Work.Final.FinalInputs`
(`Submission/Work/Final/NOTES_FINAL.md` §5): for every `x ∈ M̂` there is a chart model `G` of the
atlas with `SecNonposAt G (chart x)` and `chartGram = G` eventually near `chart x`.

The model is the field of the preferred chart of `x`; its non-positive curvature there is the
pointwise case split `ModelCurvature.secNonposAt_field_of_mem`, and the eventual agreement with
`chartGram` is `chartGram_eventually_field`. -/
theorem hmodels [rt : Work.Space.RTData] [C : ModelCurvature rt.models] :
    ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x) x), ∀ a b : Work.Space.E4,
        Submission.ChartConnection.chartGram (I := Work.Space.I4) x
          ((extChartAt Work.Space.I4 x).symm q) a b = G q a b := by
  intro x
  refine ⟨rt.models.field (rt.models.indexOf x), rt.models.field_mem_models _, ?_, ?_⟩
  · rw [extChartAt_self_eq_chart (A := rt.models) (x := x)]
    exact ModelCurvature.secNonposAt_field_chart (A := rt.models) x
  · exact chartGram_eventually_field (A := rt.models) x

/-- **The direct route to the datum.**  A provider of the atlas who has proved the sign of the
sectional curvature for each chart directly on its target gets the datum without any reference to
the three documented models. -/
theorem hmodels_of_chartSec [rt : Work.Space.RTData]
    (hsec : ∀ i : Fin rt.models.n, ∀ q ∈ (rt.models.chart i).target,
      SecNonposAt (rt.models.field i) q) :
    ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x) x), ∀ a b : Work.Space.E4,
        Submission.ChartConnection.chartGram (I := Work.Space.I4) x
          ((extChartAt Work.Space.I4 x).symm q) a b = G q a b := by
  intro x
  refine ⟨rt.models.field (rt.models.indexOf x), rt.models.field_mem_models _, ?_, ?_⟩
  · rw [extChartAt_self_eq_chart (A := rt.models) (x := x)]
    exact hsec (rt.models.indexOf x) _ ((rt.models.chart _).map_source (rt.models.indexOf_mem x))
  · exact chartGram_eventually_field (A := rt.models) x

end Work.CurvModels
