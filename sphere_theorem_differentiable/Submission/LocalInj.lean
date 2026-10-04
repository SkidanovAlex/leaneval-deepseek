import Submission.CutStep2
import Submission.InjRadius

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local injectivity of the exponential map below the injectivity radius

`Submission.CutStep2.LocallyInjectiveAtGExp hmet p w` is the hypothesis under which the cut-point step
of the Klingenberg estimate is proved: `GExp p` is injective on some neighbourhood of `w`.  This file
records the elementary half of that hypothesis: **strictly below the injectivity radius it is
automatic**.

Consequently, only the sphere `‖w‖ = m` of radius `m = inj(p)` is left
(`Submission.CutStep3.exists_two_minimising_of_hloc_sphere` uses the hypothesis there); see
`Submission/Roadmap.lean` §73.4 and §81.6 for the geometric meaning (the "fold" of the exponential
map beyond the injectivity radius).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.CutStep2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.LocalInj

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Local injectivity of `GExp p` strictly below the injectivity radius.**  If
`InjAtLeast hmet p m` and `‖w‖ < m`, then `GExp p` is injective on a neighbourhood of `w` (namely on
the ball of radius `(m - ‖w‖)/2`). -/
theorem locallyInjectiveAtGExp_of_injAtLeast (hmet : IsMetricCompatible cov) {p : M} {m : ℝ}
    (hinj : InjAtLeast hmet p m) {w : TangentSpace I p} (hw : ‖w‖ < m) :
    LocallyInjectiveAtGExp (I := I) hmet p w := by
  refine ⟨Metric.ball w ((m - ‖w‖) / 2), Metric.ball_mem_nhds w (by linarith), ?_⟩
  intro w₁ h₁ w₂ h₂ hG
  refine hinj w₁ w₂ ?_ ?_ hG
  · have hsub : ‖w₁ - w‖ < (m - ‖w‖) / 2 := by
      simpa [dist_eq_norm] using h₁
    calc ‖w₁‖ = ‖(w₁ - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖w₁ - w‖ + ‖w‖ := norm_add_le _ _
      _ < m := by linarith
  · have hsub : ‖w₂ - w‖ < (m - ‖w‖) / 2 := by
      simpa [dist_eq_norm] using h₂
    calc ‖w₂‖ = ‖(w₂ - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖w₂ - w‖ + ‖w‖ := norm_add_le _ _
      _ < m := by linarith

end

end Submission.LocalInj
