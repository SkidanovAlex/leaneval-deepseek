import Submission.UniformInj

/-!
# Joint smoothness of the exponential map in the base point and the velocity

The *base case* of the global geodesic flow: the exponential map depends smoothly on the base point
as well as on the velocity, on a ball whose radius is uniform over a compact chart piece.

The chart-flow description `GExp q (frameVector z₀ q u) = chartFlowExp D q u` is uniform over
`q ∈ Z` (`Submission.UniformInj.GExp_eq_symm_Hfun`), and `chartFlowExp` is jointly smooth in the
chart position and the chart velocity (`Submission.ChartFlowJoint.chartFlowExp_joint_contMDiffAt`);
composing with the chart `extChartAt I z₀` (which is smooth on its source) gives joint smoothness in
`(q, u)`.

## Contents

* `contMDiffAt_chartFlowExp_joint` — joint smoothness of `chartFlowExp` in `(q, u)`;
* `contMDiffOn_chartFlowExp_joint` — the `ContMDiffOn` form on a compact piece;
* `contMDiffOn_GExp_frameVector` — joint smoothness of `q ↦ GExp q (frameVector z₀ q u)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.ChartFlowJoint
open Submission.ChartFlowHom
open Submission.InjRadius
open Submission.UniformInj

namespace Submission.GExpJoint

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable {z₀ : M} {Z : Set M}

/-- **Joint smoothness of the chart-flow exponential map in the base point.** -/
theorem contMDiffAt_chartFlowExp_joint (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M}
    {u : E} (hqs : q ∈ (chartAt H z₀).source)
    (hu : ((extChartAt I z₀) q, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContMDiffAt (I.prod 𝓘(ℝ, E)) I ∞
      (fun p : M × E => chartFlowExp (cov := cov) D p.1 p.2) (q, u) := by
  have hsrc : q ∈ (extChartAt I z₀).source := by simpa using hqs
  have h1 : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) ∞
      (fun p : M × E => ((extChartAt I z₀) p.1, p.2)) (q, u) := by
    have hf : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I z₀) q :=
      (contMDiffOn_extChartAt (I := I) (x := z₀) (n := ∞)).contMDiffAt
        ((chartAt H z₀).open_source.mem_nhds hqs)
    have hf' : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : M × E => (extChartAt I z₀) p.1) (q, u) :=
      hf.comp (q, u) contMDiffAt_fst
    have hg : ContMDiffAt (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun p : M × E => p.2) (q, u) :=
      contMDiffAt_snd
    exact hf'.prodMk_space hg
  have h2 : ContMDiffAt 𝓘(ℝ, E × E) I ∞
      (fun zw : E × E => (extChartAt I z₀).symm
        ((D.α (zw.1, flowScale D • zw.2) (flowScale D)⁻¹).1))
      ((extChartAt I z₀) q, u) :=
    chartFlowExp_joint_contMDiffAt (cov := cov) (I := I) D hu
  have hres := h2.comp (q, u) h1
  simpa only [chartFlowExp_apply, Function.comp_def] using hres

/-- **Joint smoothness of the chart-flow exponential map on a compact chart piece.** -/
theorem contMDiffOn_chartFlowExp_joint (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    (hZsrc : Z ⊆ (chartAt H z₀).source) {η : ℝ} (hηc : η ≤ 1 / (2 * flowScale D)) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) I ∞
      (fun p : M × E => chartFlowExp (cov := cov) D p.1 p.2)
      (Z ×ˢ Metric.closedBall (0 : E) η) := by
  intro p hp
  have hqs : p.1 ∈ (chartAt H z₀).source := hZsrc hp.1
  have hcpos : 0 < flowScale D := flowScale_pos D
  have h2c : (0 : ℝ) < 2 * flowScale D := by linarith
  have hmem : ((extChartAt I z₀) p.1, flowScale D • p.2) ∈ chartData (I := I) z₀ Z := by
    refine ⟨⟨p.1, hp.1, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcpos]
    have h1 : ‖p.2‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hp.2
    have h2 : flowScale D * η ≤ 1 / 2 := by
      rw [le_div_iff₀ h2c] at hηc
      nlinarith [hηc, hcpos]
    nlinarith [h1, h2, norm_nonneg p.2, hcpos]
  exact (contMDiffAt_chartFlowExp_joint (cov := cov) D hqs hmem).contMDiffWithinAt

/-- **Joint smoothness of the exponential map in the base point and the velocity**, in the
coordinates of a fixed chart: the map `(q, u) ↦ GExp q (frameVector z₀ q u)` is `C^∞` on the
product of a compact chart piece with a ball of coordinate velocities. -/
theorem contMDiffOn_GExp_frameVector (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (hZsrc : Z ⊆ (chartAt H z₀).source)
    {η : ℝ} (hηc : η ≤ 1 / (2 * flowScale D)) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) I ∞
      (fun p : M × E => GExp (cov := cov) hmet p.1 (frameVector (I := I) z₀ p.1 p.2))
      (Z ×ˢ Metric.closedBall (0 : E) η) := by
  have hchart := contMDiffOn_chartFlowExp_joint (cov := cov) D hZsrc hηc
  refine hchart.congr ?_
  rintro ⟨q, u⟩ ⟨hqZ, hu⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
  have hqs : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hqZ
  have hcpos : 0 < flowScale D := flowScale_pos D
  have h2c : (0 : ℝ) < 2 * flowScale D := by linarith
  have hphase : ((extChartAt I z₀) q, flowScale D • u) ∈ D.O :=
    D.hKO ⟨⟨q, hqZ, rfl⟩, by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos hcpos]
      have h2 : flowScale D * η ≤ 1 / 2 := by
        rw [le_div_iff₀ h2c] at hηc
        nlinarith [hηc, hcpos]
      nlinarith [hu, h2, norm_nonneg u, hcpos]⟩
  exact GExp_eq_symm_Hfun (cov := cov) hmet D hqZ hqs hphase

/-! ## The ray structure of the chart-flow model -/

/-- **The chart-flow model restricted to a ray is a flow line.**  For `r ∈ [0,1]` the point of the
ray at coordinate `r • u` is the position component of the chart flow started at
`(φ q, c • u)` (with `c = flowScale D`, `φ = extChartAt I z₀`) after flow time `r * c⁻¹`. -/
theorem chartFlowExp_smul_ray (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M}
    {u : E} (hcuO : ((extChartAt I z₀) q, flowScale D • u) ∈ D.O)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrO : ((extChartAt I z₀) q, r • (flowScale D • u)) ∈ D.O) :
    chartFlowExp (cov := cov) D q (r • u)
      = (extChartAt I z₀).symm
          ((D.α ((extChartAt I z₀) q, flowScale D • u) (r * (flowScale D)⁻¹)).1) := by
  rw [chartFlowExp_apply]
  have habs : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have ht : |(flowScale D)⁻¹| ≤ D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hsm : flowScale D • (r • u) = r • (flowScale D • u) := smul_comm _ _ _
  rw [hsm]
  rw [chartFlowData_homogeneous (cov := cov) (I := I) D (q := (extChartAt I z₀) q)
    (v := flowScale D • u) (c := r) (t := (flowScale D)⁻¹) habs hrO hcuO ht]

end

end Submission.GExpJoint
