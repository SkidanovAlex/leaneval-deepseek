import Submission.UnifDeps
import Submission.ChartBallBarrier
import Submission.BarrierComparison
import Submission.BalayageSubharmonic
import Submission.ChartLogClamp
import Submission.DirichletX
import Submission.GreenFunction

/-!
# Dirichlet regularity at the sphere of a chart ball

The explicit barrier `Submission.chartBallBarrier c a ρ = (ρ - ‖c · - a‖)/ρ` is superharmonic on
the chart ball `chartBall c a ρ` and tends to `0` at every point of the chart sphere
`chartSphere c a ρ`.  Feeding it into the abstract barrier comparison
`Submission.limEnvelope_le_of_superharmonic_bound` gives the **Dirichlet regularity of the chart
ball** for the limsup region-Perrron family with zero boundary data:

`limEnvelope (chartBall c a ρ) 0 M` is harmonic on the chart ball, and tends to `0` at every point
of the chart sphere.

This is the template for every region built from chart balls; it is the ingredient of the region
Green functions of the exhaustion construction.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The frontier of a chart ball -/

/-- The closure of a chart ball is compact, provided the closed Euclidean ball lies in the target
of the chart. -/
theorem isCompact_closure_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) : IsCompact (closure (chartBall c a ρ)) :=
  ((isCompact_closedBall a ρ).image_of_continuousOn (c.continuousOn_symm.mono hsub)).of_isClosed_subset
    isClosed_closure (closure_chartBall_subset hsub)

/-- The chart sphere is part of the frontier of the chart ball. -/
theorem chartSphere_subset_frontier_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    chartSphere c a ρ ⊆ frontier (chartBall c a ρ) := by
  intro ξ hξ
  obtain ⟨hsrc, hsph⟩ := mem_chartSphere.mp hξ
  rw [frontier, Set.mem_diff, (chartBall_isOpen c a ρ).interior_eq]
  refine ⟨?_, ?_⟩
  · rw [closure_chartBall_eq_chartClosedBall hρ hsub]
    exact ⟨hsrc, Metric.sphere_subset_closedBall hsph⟩
  · intro hmem
    rw [mem_chartBall] at hmem
    rw [Metric.mem_sphere, dist_eq_norm] at hsph
    have hb := Metric.mem_ball.mp hmem.2
    rw [dist_eq_norm] at hb
    linarith

/-- The frontier of a chart ball of positive radius is non-empty: the chart image of `a + ρ` is a
frontier point. -/
theorem frontier_chartBall_nonempty {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    (frontier (chartBall c a ρ)).Nonempty := by
  have hmem : a + (ρ : ℂ) ∈ Metric.closedBall a ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
  refine ⟨c.symm (a + (ρ : ℂ)), chartSphere_subset_frontier_chartBall hρ hsub ?_⟩
  rw [mem_chartSphere]
  refine ⟨c.map_target (hsub hmem), ?_⟩
  rw [c.right_inv (hsub hmem), Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]

/-! ## The barrier tends to zero at the chart sphere -/

/-- The barrier is continuous at every point of the chart source. -/
theorem continuousAt_chartBallBarrier {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) {x : X} (hx : x ∈ c.source) : ContinuousAt (chartBallBarrier c a ρ) x := by
  have h1 : ContinuousAt (fun y : X => c y - a) x := (c.continuousAt hx).sub continuousAt_const
  have h2 : ContinuousAt (fun y : X => ‖c y - a‖) x := h1.norm
  have h3 : ContinuousAt (fun y : X => (ρ - ‖c y - a‖) / ρ) x :=
    (continuousAt_const.sub h2).div_const ρ
  have h4 : ContinuousAt (fun y : X => max 0 ((ρ - ‖c y - a‖) / ρ)) x := by
    have h5 := (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x).sup h3
    simpa only [Pi.sup_apply, Pi.zero_apply] using h5
  refine h4.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  exact (chartBallBarrier_of_mem_source hy).symm

/-- A point of the chart sphere is a zero of the barrier. -/
theorem chartBallBarrier_eq_zero_of_mem_chartSphere {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) {ξ : X} (hξ : ξ ∈ chartSphere c a ρ) :
    chartBallBarrier c a ρ ξ = 0 := by
  obtain ⟨hsrc, hsph⟩ := mem_chartSphere.mp hξ
  rw [chartBallBarrier_of_mem_source hsrc]
  have hnorm : ‖c ξ - a‖ = ρ := by
    rw [Metric.mem_sphere, dist_eq_norm] at hsph
    exact hsph
  rw [hnorm, sub_self, zero_div]
  exact max_eq_left (le_refl 0)

/-- The barrier tends to `0` at every point of the chart sphere. -/
theorem tendsto_chartBallBarrier {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {ξ : X} (hξ : ξ ∈ chartSphere c a ρ) :
    Filter.Tendsto (chartBallBarrier c a ρ) (𝓝 ξ) (𝓝 0) := by
  obtain ⟨hsrc, -⟩ := mem_chartSphere.mp hξ
  rw [← chartBallBarrier_eq_zero_of_mem_chartSphere hρ hξ]
  exact (continuousAt_chartBallBarrier hρ hsrc).tendsto

end Submission

/-! ## The region-Dirichlet problem on a chart ball -/

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The barrier comparison on a chart ball**: the Perron envelope of the region-Dirichlet
problem with zero boundary data on a chart ball is bounded by `M` times the barrier. -/
theorem limEnvelope_chartBall_le {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ M : ℝ}
    (hc : c ∈ atlas ℂ X) (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) (hM : 0 ≤ M)
    (hne : (limFamily (chartBall c a ρ) (fun _ : X => 0) M).Nonempty) :
    ∀ x ∈ chartBall c a ρ,
      limEnvelope (chartBall c a ρ) (fun _ : X => 0) M x ≤ M * chartBallBarrier c a ρ x :=
  limEnvelope_le_of_superharmonic_bound (chartBall_isOpen c a ρ) (isCompact_closure_chartBall hsub)
    (frontier_chartBall_nonempty hρ hsub) hne
    (Submission.SuperharmonicOnX.const_mul (u := chartBallBarrier c a ρ) hM
      (superharmonicOnX_chartBallBarrier hc hρ))
    (fun x _ => mul_nonneg hM (chartBallBarrier_nonneg c a ρ x))
    (fun _ _ => le_refl 0)

/-- The zero function is a member of the region-Perrron family with zero boundary data (when
`0 ≤ M`). -/
theorem zero_mem_limFamily {U : Set X} {M : ℝ} (hM : 0 ≤ M) :
    (fun _ : X => (0 : ℝ)) ∈ limFamily U (fun _ : X => 0) M :=
  ⟨(subharmonicOnX_const 0).mono (subset_univ U) continuousOn_const, fun x => hM,
    fun _ _ ε hε => by filter_upwards with z; linarith⟩

/-- **Dirichlet regularity at the sphere of a chart ball**: with zero boundary data the Perron
envelope tends to `0` at every point of the chart sphere. -/
theorem limEnvelope_chartBall_tendsto {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ M : ℝ}
    (hc : c ∈ atlas ℂ X) (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) (hM : 0 ≤ M)
    (hne : (limFamily (chartBall c a ρ) (fun _ : X => 0) M).Nonempty) :
    ∀ ξ ∈ chartSphere c a ρ,
      Filter.Tendsto (limEnvelope (chartBall c a ρ) (fun _ : X => 0) M)
        (𝓝[chartBall c a ρ] ξ) (𝓝 0) := by
  intro ξ hξ
  have hle := limEnvelope_chartBall_le hc hρ hsub hM hne
  have hperron := limFamily_isPerronOn (chartBall_isOpen c a ρ) hne
  have hge : ∀ x ∈ chartBall c a ρ,
      0 ≤ limEnvelope (chartBall c a ρ) (fun _ : X => 0) M x :=
    fun x hx => limFamily_le_limEnvelope (chartBall_isOpen c a ρ) hne
      (zero_mem_limFamily hM) x hx
  have hlow : Filter.Tendsto (fun _ : X => (0 : ℝ)) (𝓝[chartBall c a ρ] ξ) (𝓝 0) :=
    tendsto_const_nhds
  have hhigh : Filter.Tendsto (fun x : X => M * chartBallBarrier c a ρ x)
      (𝓝[chartBall c a ρ] ξ) (𝓝 0) := by
    have hbase : Filter.Tendsto (fun x : X => M * chartBallBarrier c a ρ x) (𝓝 ξ) (𝓝 0) := by
      simpa using (tendsto_chartBallBarrier hρ hξ).const_mul M
    exact hbase.mono_left inf_le_left
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hge x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hle x hx

end Submission
