import Mathlib
import Submission.Work.Space.MetricChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-
# The metric in the chart at `x` is the model of the chart at `x`

`Work.Space.ModelAtlas.chartGram_eq_model` states that, on a neighbourhood of `x`, the metric
`chartGram x` expressed in the chart at `x` agrees with the model `A.model (A.indexOf x)` evaluated
at the chart coordinates.  Composing with the (definitional) identification of the extended chart
`extChartAt I4 x` with `chartAt E4 x` for the trivial model with corners `I4 = 𝓘(ℝ, E4)`, this is
exactly the statement needed downstream: the metric in the chart at `x` is the *field*
`A.field (A.indexOf x)` of the atlas, the model attached to the chart of `x`.

This is the hypothesis form used by `Work.Curvature.curvLe_of_models`.
-/

noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle
open Bundle

namespace Work.CurvModels

/-- **The metric in the chart at `x` is the field of the chart at `x`.** -/
theorem chartGram_eventually_field {M : Type*} [TopologicalSpace M] [T2Space M]
    [A : Work.Space.ModelAtlas M] [IsManifold Work.Space.I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [IsManifold Work.Space.I4 1 M] [A.HasIsometry] (x : M) :
    ∀ᶠ q in nhds ((extChartAt Work.Space.I4 x) x), ∀ a b : Work.Space.E4,
      Submission.ChartConnection.chartGram (I := Work.Space.I4) x
        ((extChartAt Work.Space.I4 x).symm q) a b = A.field (A.indexOf x) q a b := by
  have hx : (extChartAt Work.Space.I4 x) x = chartAt Work.Space.E4 x x := by simp
  have hs : ∀ q : Work.Space.E4,
      (extChartAt Work.Space.I4 x).symm q = (chartAt Work.Space.E4 x).symm q := by
    intro q; simp
  rw [hx]
  have hcont : ContinuousAt (chartAt Work.Space.E4 x).symm (chartAt Work.Space.E4 x x) :=
    ContinuousOn.continuousAt ((chartAt Work.Space.E4 x).continuousOn_invFun)
      ((chartAt Work.Space.E4 x).open_target.mem_nhds (mem_chart_target Work.Space.E4 x))
  have hxa : (chartAt Work.Space.E4 x).symm (chartAt Work.Space.E4 x x) = x :=
    (chartAt Work.Space.E4 x).left_inv (mem_chart_source Work.Space.E4 x)
  obtain ⟨U, hU, hUsub⟩ :=
    (eventually_iff_exists_mem).mp (Work.Space.ModelAtlas.chartGram_eq_model (A := A) x)
  filter_upwards [hcont.eventually (hxa ▸ hU),
    (chartAt Work.Space.E4 x).open_target.mem_nhds
      (mem_chart_target Work.Space.E4 x)] with q hq hqT
  intro a b
  rw [hs q]
  rw [hUsub ((chartAt Work.Space.E4 x).symm q) hq a b, (chartAt Work.Space.E4 x).right_inv hqT]
  rfl

end Work.CurvModels
