import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.scal_rot
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.flowContAtZeroScal_of_isRicciFlow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The scalar curvature in the coordinate frame of the chart at `x₀`.**

For any smooth family of metrics `G`, any `t`, any chart centre `x₀` and any point `y` in the
chart at `x₀`, the scalar curvature `scalAt (G t) y` equals the contraction `N2` of the
coordinate-frame curvature components `rmC4` with the inverse Gram matrix `GramM`.

This is the specialisation of the general-basis statement
`Work.Diff.GE.ScalK.scalAt_eq_N2_of_basis` to the coordinate frame `cFrame x₀ ·`, whose Gram
matrix is `GramM` by definition and which spans the tangent space at every point of the chart
source (`Work.Diff.GE.ScalK.cFrame_span`). -/
theorem scalAt_eq_N2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) {x₀ : M} (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    scalAt (G t) y
      = N2 (GramM (I := I) G x₀ t y) (rmC4 (I := I) G x₀ t y) := by
  refine ScalK.scalAt_eq_N2_of_basis (I := I) hLC y
    (fun i => cFrame (I := I) x₀ i y) (GramM (I := I) G x₀ t y) (fun i j => rfl)
    (ScalK.cFrame_span (I := I) x₀ hy)

end Work.Diff.GE
