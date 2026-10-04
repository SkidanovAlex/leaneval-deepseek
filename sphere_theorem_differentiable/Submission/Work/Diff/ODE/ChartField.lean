import Mathlib
import Submission.Work.Diff.ODE.Basic
import Submission.Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz
import Submission.Commons.Analysis.ODE.uniform_flow_joint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coordinate expression of a time-dependent vector field

This file provides the single definition shared by the ODE-area lemmas about the local flow of a
time-dependent vector field `X` on a manifold: the **chart field**
`chartField X x₀ : ℝ × E → E`, which reads `X a q` in the tangent-bundle trivialisation at `x₀`
and in the chart at `x₀`.

If `p = (a, v)` with `v` in the target of the chart at `x₀`, then `chartField X x₀ p` is the
coordinate vector at the chart point `v` of the vector `X a (chart⁻¹ v)`.

As a convenience for the ODE area, this module also re-exports the small pieces of the commons that
the local-flow arguments need (`hasMFDerivAt_extChartAt_symm_comp`,
`eqOn_of_hasDerivAt_of_locallyLipschitz`, `uniform_flow_joint`).
-/

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Set Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The coordinate expression of the time-dependent vector field `X` in the chart at `x₀`: at
`p = (a, v)` it is the coordinate vector of `X a (chart⁻¹ v)` in the tangent-bundle trivialisation
at `x₀` (and it is the junk value `0` if `v` is not in the chart target). -/
noncomputable def chartField (X : ℝ → Π x : M, TangentSpace I x) (x₀ : M) : ℝ × E → E :=
  fun p => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
    ((extChartAt I x₀).symm p.2) (X p.1 ((extChartAt I x₀).symm p.2))

end Work.Diff.ODE
