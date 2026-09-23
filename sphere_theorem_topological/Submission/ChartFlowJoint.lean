import Submission.GExpFlow

/-!
# Joint smoothness of the chart-flow exponential map in (base point, velocity)

`Submission.GExpFlow.chartFlowExp_contMDiffAt` proves that the chart-flow exponential map
`u ↦ chartFlowExp D q u` is smooth at `u` for a *fixed* base point `q`.  A continuation argument
along a ray, however, has to move the base point as well: after one step one restarts the flow at
the point that has just been reached.  This file provides the corresponding **joint** statement, in
*coordinates*: the map

  `(x, u) ↦ (extChartAt I z₀).symm ((D.α (x, c • u) c⁻¹).1)`,   `c = flowScale D`,

from `E × E` (chart position, chart velocity) to `M`, is `C^∞` at every pair whose phase
`(x, c • u)` lies in the flow data `chartData z₀ Z` (i.e. `x` a chart position of `Z` and the
velocity of coordinate norm at most `1`).  The only input is the joint smoothness
`ChartFlowData.hjoint` of the flow itself, which is precisely the statement that the spray flow
depends smoothly on its initial condition.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.RauchGen
open Submission.GExpFlow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ChartFlowJoint

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- **Joint smoothness of the chart flow in (phase, time-independent form).** -/
theorem chartFlow_state_contDiffAt (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : E}
    (hK : (x, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContDiffAt ℝ ∞ (fun zw : E × E => D.α (zw.1, flowScale D • zw.2) (flowScale D)⁻¹) (x, u) := by
  set c : ℝ := flowScale D with hcdef
  have hcinv : c⁻¹ = D.ρ / 2 := by rw [hcdef]; exact inv_flowScale D
  have ht : |c⁻¹| < D.ρ := by
    rw [hcinv, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hjoint := D.hjoint (x, c • u) hK (c⁻¹) ht
  have hinner : ContDiffAt ℝ ∞ (fun zw : E × E => ((zw.1, c • zw.2), c⁻¹)) (x, u) :=
    (contDiffAt_id.fst.prodMk (contDiffAt_const.smul contDiffAt_id.snd)).prodMk
      (contDiffAt_const (c := c⁻¹))
  have h := ContDiffAt.comp (x := (x, u)) hjoint hinner
  simpa only [Function.comp_def, hcdef] using h

/-- **Joint smoothness of the chart-flow exponential map** in the chart position and the chart
velocity. -/
theorem chartFlowExp_joint_contMDiffAt (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : E}
    (hK : (x, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContMDiffAt 𝓘(ℝ, E × E) I ∞
      (fun zw : E × E => (extChartAt I z₀).symm
        ((D.α (zw.1, flowScale D • zw.2) (flowScale D)⁻¹).1)) (x, u) := by
  set c : ℝ := flowScale D with hcdef
  have hcinv : c⁻¹ = D.ρ / 2 := by rw [hcdef]; exact inv_flowScale D
  have hO : (x, c • u) ∈ D.O := D.hKO hK
  have hcomp : ContDiffAt ℝ ∞ (fun zw : E × E => (D.α (zw.1, c • zw.2) (c⁻¹)).1) (x, u) :=
    (chartFlow_state_contDiffAt (cov := cov) (I := I) D hK).fst
  have hmem : (D.α (x, c • u) (c⁻¹)).1 ∈ (extChartAt I z₀).target :=
    D.htgt (x, c • u) hO (c⁻¹) (by
      rw [hcinv, abs_of_pos (div_pos D.hρ two_pos)]; linarith [D.hρ])
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I z₀).symm
      ((D.α (x, c • u) (c⁻¹)).1) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).contMDiffAt
      ((isOpen_extChartAt_target z₀).mem_nhds hmem)
  have hres := hsymm.comp (x, u) (hcomp.contMDiffAt)
  simpa only [Function.comp_def, hcdef] using hres

end

end Submission.ChartFlowJoint
