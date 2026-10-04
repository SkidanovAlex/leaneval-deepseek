import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Distance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.EXT.AuxL

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The chart matrix of a fixed smooth metric is continuous at the chart centre: each matrix entry `y ↦ chartMatFun g x₀ y i j` is continuous at `(extChartAt I x₀) x₀`.

Route: after `letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩` (and `haveI : IsContMDiffRiemannianBundle I ∞ E _ := inferInstance`), `chartMatFun g x₀ y i j` is, by `rfl`, `Submission.ChartConnection.chartGram x₀ ((extChartAt I x₀).symm y) (bB i) (bB j)`; compose `Submission.Distance.continuousAt_chartGram` (which needs only `x₀ ∈ (chartAt H x₀).source`) with Mathlib's `continuousAt_extChartAt_symm` at the chart centre. -/
theorem chartMatFun_continuousAt_centre
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun y : E => Work.Diff.EXT.chartMatFun g x₀ y i j) ((extChartAt I x₀) x₀) := by
  -- register the instance metric induced by `g`, so that `chartGram` refers to `g`
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x) := inferInstance
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  -- the inverse extended chart sends the chart centre back to `x₀`
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
    PartialEquiv.left_inv _ (by rw [extChartAt_source]; exact hx₀)
  -- hence the chart Gram entry is continuous at `x₀`
  have hgc : ContinuousAt
      (fun q : M => Submission.ChartConnection.chartGram (I := I) x₀ q
        (Work.Diff.EXT.bB (E := E) i) (Work.Diff.EXT.bB (E := E) j))
      ((extChartAt I x₀).symm ((extChartAt I x₀) x₀)) := by
    rw [hsymm]
    exact Submission.Distance.continuousAt_chartGram (I := I) x₀ _ _ hx₀
  -- compose with the (continuous) inverse chart
  have hgram : ContinuousAt
      (fun y : E => Submission.ChartConnection.chartGram (I := I) x₀
        ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i) (Work.Diff.EXT.bB (E := E) j))
      ((extChartAt I x₀) x₀) :=
    hgc.comp (continuousAt_extChartAt_symm (I := I) x₀)
  -- and identify the chart matrix with the chart Gram entry
  refine hgram.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  rfl

end Work.Diff.EXT.AuxL
