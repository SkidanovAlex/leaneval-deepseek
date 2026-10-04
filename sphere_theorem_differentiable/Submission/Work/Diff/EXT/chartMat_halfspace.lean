import Submission.Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart matrix on a time half-space

`Work.Diff.EXT.chartMat G x₀ t y` is the matrix of the metric `G t` in the coordinate frame of the
chart at `x₀`, evaluated at the chart coordinate `y`.  The companion module
`contDiffWithinAt_chartMat_of_jointSmooth` proves that, when `G` is jointly smooth on a time set `J`
(for the continuation theorem `J = [0, T)`, so the smoothness in time is one-sided at `t = 0`), the
function `(t, y) ↦ chartMat G x₀ t y` is `C^∞` **within** `J ×ˢ (extChartAt I x₀).target`.

This module used to contain a second, independently written copy of that proof, in which the
general-point theorem carried the *plain* name `contDiffWithinAt_chartMat_of_jointSmooth`; as a
consequence no module could import both this file and `contDiffWithinAt_chartMat_of_jointSmooth`.
The copy is retired: the general-point theorem is `contDiffWithinAt_chartMat_of_jointSmooth_gen` of
the companion module, and here we record only the half-space corollary `chartMat_halfspace` used by
the splice/restart step and by `chartMat_twoSided`, `twoSided_of_within`, ... .
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart matrix is smooth on the time half-space `[0, T)`.**  If `G` is jointly smooth on
`[0, T)`, then in the chart at `x₀` the chart matrix is `C^∞` on the slab
`[0, T) × (extChartAt I x₀).target`.  This is the form used by the splice/restart step, where the
family is only known to be smooth up to `t = 0`. -/
theorem chartMat_halfspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T)) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      ((Set.Ico 0 T) ×ˢ (extChartAt I x₀).target) :=
  fun p hp => contDiffWithinAt_chartMat_of_jointSmooth_gen hG hp.1 x₀ hp.2

end Work.Diff.EXT
