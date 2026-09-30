/-
# `chartGram` in the chart of a point is the model of that chart

This file connects the metric of `Work.Space.Metric` to the chartwise metric `chartGram` of the
vendored library (`Submission.Work.RiemLib.ChartConnection`): on a neighbourhood of `x`, the metric
expressed in the chart at `x` is exactly the model of the chart at `x`.

This is the **exact hypothesis of `Work.Curvature.curvLe_of_models`** (blueprint §3, CURV Part 2):
for every point `x` there is a model `G` of the atlas with
`chartGram x ((extChartAt I4 x).symm q) a b = G q a b` for all `q` near `extChartAt I4 x x`.

## Main results

* `Work.Space.ModelAtlas.chartGram_eq_model` — the pointwise form
  `chartGram x y a b = model_{i(x)} (chartAt x y) a b` for `y` near `x`.
* `Work.Space.ModelAtlas.chartGram_is_model` — the form used by `Curvature.curvLe_of_models`.
-/
import Mathlib
import Submission.Work.Space.MetricBundle
import Submission.Work.RiemLib.ChartConnection

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle
open Bundle

namespace Work.Space

namespace ModelAtlas

variable {M : Type*} [TopologicalSpace M] [T2Space M] [A : ModelAtlas M]
  [IsManifold I4 ∞ M] [IsManifold I4 1 M] [A.HasIsometry]

/-- **The metric in the chart at `x` is the model of the chart at `x`.** -/
theorem chartGram_eq_model (x : M) :
    ∀ᶠ y in 𝓝 x, ∀ a b : E4,
      Submission.ChartConnection.chartGram (I := I4) x y a b
        = A.model (A.indexOf x) (chartAt E4 x y) a b := by
  filter_upwards [ModelAtlas.HasIsometry.out (A := A) x,
    (chartAt E4 x).open_source.mem_nhds (mem_chart_source E4 x)] with y hiso hy
  intro a b
  have hL : Submission.ChartConnection.chartGram (I := I4) x y a b
      = (A.model (A.indexOf y) (chartAt E4 y y)
          : TangentSpace I4 y →L[ℝ] TangentSpace I4 y →L[ℝ] ℝ)
          (Submission.Geodesic.frameVector (I := I4) x y a)
          (Submission.Geodesic.frameVector (I := I4) x y b) := rfl
  have hf : ∀ a : E4, Submission.Geodesic.frameVector (I := I4) x y a
      = (tangentCoordChange I4 x y y a : TangentSpace I4 y) := fun a =>
    symmL_trivializationAt_eq (A := A.toFinAtlas) x y hy a
  rw [hL, hf a, hf b]
  exact hiso a b

/-- **`chartGram` is a model** — the exact form of the hypothesis of
`Work.Curvature.curvLe_of_models`. -/
theorem chartGram_is_model (x : M) :
    ∃ G ∈ A.models, ∀ᶠ q in 𝓝 ((extChartAt I4 x) x), ∀ a b : E4,
      Submission.ChartConnection.chartGram (I := I4) x ((extChartAt I4 x).symm q) a b
        = G q a b := by
  refine ⟨A.field (A.indexOf x), A.field_mem_models _, ?_⟩
  have hx : (extChartAt I4 x) x = chartAt E4 x x := by
    simp [extChartAt_coe, modelWithCornersSelf_coe]
  have hs : ∀ q : E4, (extChartAt I4 x).symm q = (chartAt E4 x).symm q := by
    intro q
    simp [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  rw [hx]
  have hcont : ContinuousAt (chartAt E4 x).symm (chartAt E4 x x) :=
    ContinuousOn.continuousAt ((chartAt E4 x).continuousOn_invFun)
      ((chartAt E4 x).open_target.mem_nhds (mem_chart_target E4 x))
  have hxa : (chartAt E4 x).symm (chartAt E4 x x) = x :=
    (chartAt E4 x).left_inv (mem_chart_source E4 x)
  obtain ⟨U, hU, hUsub⟩ := (eventually_iff_exists_mem).mp (A.chartGram_eq_model x)
  filter_upwards [hcont.eventually (hxa ▸ hU),
    (chartAt E4 x).open_target.mem_nhds (mem_chart_target E4 x)] with q hq hqT
  intro a b
  rw [hs q]
  rw [hUsub ((chartAt E4 x).symm q) hq a b, (chartAt E4 x).right_inv hqT]
  rfl

end ModelAtlas

end Work.Space
