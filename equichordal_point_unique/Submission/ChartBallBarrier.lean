import Submission.UnifDeps
import Submission.RiemannSurface
import Submission.SuperharmonicX
import Submission.Commons.Analysis.Complex.Analytic.norm_le_circleAverage

/-!
# The chart-ball barrier `(ρ - ‖c · - a‖)/ρ`

The Dirichlet problem on a chart ball `chartBall c a ρ` has an *explicit* barrier: the function
`x ↦ (ρ - ‖c x - a‖)/ρ`, which is `0` on the chart sphere, positive inside, and superharmonic
(it is `1 - ‖F‖/ρ` for the holomorphic chart map `F = c - a`).

This module constructs that barrier globally on `X` by clamping it to `0` outside the chart source,

`Submission.chartBallBarrier c a ρ = fun x => if x ∈ c.source then max 0 ((ρ - ‖c x - a‖)/ρ) else 0`,

and proves that it is superharmonic on the chart ball:

`Submission.superharmonicOnX_chartBallBarrier (hc : c ∈ atlas ℂ X) (hρ : 0 < ρ) :
   SuperharmonicOnX (chartBallBarrier c a ρ) (chartBall c a ρ)`.

The superharmonicity is proved in the chart `c` itself and then transported to the preferred charts
`chartAt ℂ x` by `Submission.SuperharmonicAtChart.transport` (chart independence of
superharmonicity), the analyticity of the chart transitions being supplied by
`Submission.analyticAt_transition_of_mem_atlas`.

Together with `Submission.limEnvelope_le_of_superharmonic_bound` this gives the boundary regularity
of the region-Dirichlet problem on a chart ball with zero boundary data: the Perron envelope of
`limFamily (chartBall c a ρ) f M` (with `f ≤ 0` on the sphere) is bounded by `M · chartBallBarrier`,
hence tends to `0` at every point of the chart sphere.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## Chart transitions of atlas members are analytic -/

section Transition

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart transitions of arbitrary atlas members are complex analytic.**  This is the
atlas-general version of `Commons.Geometry.Manifold.chart_transition_analyticOnNhd`: the change of
coordinates `z ↦ c (d.symm z)` between two charts `c d` of the atlas of a complex one-manifold is
analytic at every point where it is defined. -/
theorem analyticAt_transition_of_mem_atlas {c d : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ atlas ℂ X) (hd : d ∈ atlas ℂ X) :
    ∀ z : ℂ, z ∈ d.target → d.symm z ∈ c.source →
      AnalyticAt ℂ (fun z : ℂ => c (d.symm z)) z := by
  intro z hzt hzs
  have hG : d.symm.trans c ∈ contDiffGroupoid (1 : ℕ∞ω) (modelWithCornersSelf ℂ ℂ) :=
    StructureGroupoid.compatible (contDiffGroupoid (1 : ℕ∞ω) (modelWithCornersSelf ℂ ℂ)) hd hc
  have hcd : ContDiffOn ℂ (1 : ℕ∞ω) (d.symm.trans c) (d.symm.trans c).source := by
    rw [contDiffGroupoid] at hG
    rw [mem_groupoid_of_pregroupoid] at hG
    simpa [contDiffPregroupoid] using hG.1
  have hdiff : DifferentiableOn ℂ (d.symm.trans c) (d.symm.trans c).source :=
    hcd.differentiableOn_one
  have hana : AnalyticOnNhd ℂ (d.symm.trans c) (d.symm.trans c).source :=
    hdiff.analyticOnNhd (d.symm.trans c).open_source
  have hzs' : z ∈ (d.symm.trans c).source := mem_trans_source.mpr ⟨hzt, hzs⟩
  refine (hana z hzs').congr ?_
  filter_upwards [(d.symm.trans c).open_source.mem_nhds hzs'] with w _
  show (d.symm.trans c) w = c (d.symm w)
  rw [OpenPartialHomeomorph.trans_apply]

end Transition

/-! ## The barrier -/

section Barrier

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The chart-ball barrier**: `(ρ - ‖c x - a‖)/ρ` on the chart ball `chartBall c a ρ`, clamped
to `0` outside the source of the chart. -/
noncomputable def chartBallBarrier (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : X → ℝ :=
  fun x => if x ∈ c.source then max 0 ((ρ - ‖c x - a‖) / ρ) else 0

theorem chartBallBarrier_of_mem_source {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {x : X}
    (hx : x ∈ c.source) :
    chartBallBarrier c a ρ x = max 0 ((ρ - ‖c x - a‖) / ρ) := if_pos hx

theorem chartBallBarrier_of_not_mem_source {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {x : X} (hx : x ∉ c.source) : chartBallBarrier c a ρ x = 0 := if_neg hx

/-- On the chart ball, the barrier is the unclamped expression `(ρ - ‖c x - a‖)/ρ`. -/
theorem chartBallBarrier_of_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {x : X} (hx : x ∈ chartBall c a ρ) :
    chartBallBarrier c a ρ x = (ρ - ‖c x - a‖) / ρ := by
  rw [chartBallBarrier_of_mem_source hx.1, max_eq_right]
  have h := Metric.mem_ball.mp hx.2
  rw [dist_eq_norm] at h
  exact div_nonneg (sub_nonneg.mpr h.le) hρ.le

theorem chartBallBarrier_nonneg (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (x : X) :
    0 ≤ chartBallBarrier c a ρ x := by
  by_cases hx : x ∈ c.source
  · rw [chartBallBarrier_of_mem_source hx]; exact le_max_left _ _
  · rw [chartBallBarrier_of_not_mem_source hx]

/-- The barrier is bounded by `1` everywhere. -/
theorem chartBallBarrier_le_one {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (x : X) : chartBallBarrier c a ρ x ≤ 1 := by
  by_cases hx : x ∈ c.source
  · rw [chartBallBarrier_of_mem_source hx]
    refine max_le (by norm_num) ?_
    rw [div_le_one hρ]
    exact sub_le_self ρ (norm_nonneg _)
  · rw [chartBallBarrier_of_not_mem_source hx]; norm_num

/-- The barrier is continuous on the chart ball. -/
theorem continuousOn_chartBallBarrier (c : OpenPartialHomeomorph X ℂ) (a : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) : ContinuousOn (chartBallBarrier c a ρ) (chartBall c a ρ) := by
  have hnorm : ContinuousOn (fun x : X => ‖c x - a‖) (chartBall c a ρ) :=
    ((c.continuousOn.mono (chartBall_subset_source c a ρ)).sub continuousOn_const).norm
  have hf : ContinuousOn (fun x : X => (ρ - ‖c x - a‖) / ρ) (chartBall c a ρ) :=
    (continuousOn_const.sub hnorm).div_const ρ
  exact hf.congr (fun x hx => show chartBallBarrier c a ρ x = (ρ - ‖c x - a‖) / ρ from
    chartBallBarrier_of_mem hρ hx)

/-- **The barrier is superharmonic on the chart ball, measured in the chart `c` itself.** -/
theorem superharmonicAtChart_chartBallBarrier (c : OpenPartialHomeomorph X ℂ) (a : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) {x : X} (hx : x ∈ chartBall c a ρ) :
    SuperharmonicAtChart (chartBallBarrier c a ρ) c x := by
  obtain ⟨hxsrc, hxball⟩ := hx
  have hxnorm : ‖c x - a‖ < ρ := by
    have h := Metric.mem_ball.mp hxball
    rwa [dist_eq_norm] at h
  have hδ : 0 < ρ - ‖c x - a‖ := sub_pos.mpr hxnorm
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hxsrc))
  set ρ' : ℝ := min ε ((ρ - ‖c x - a‖) / 2) with hρ'def
  have hρ' : 0 < ρ' := lt_min hε (by linarith)
  have hρ'ε : ρ' ≤ ε := min_le_left _ _
  have hρ'δ : ρ' ≤ (ρ - ‖c x - a‖) / 2 := min_le_right _ _
  have hρ'lt : ρ' < ρ - ‖c x - a‖ := by linarith
  have htgt : Metric.ball (c x) ρ' ⊆ c.target := (Metric.ball_subset_ball hρ'ε).trans hεsub
  have hlt : ∀ w ∈ Metric.ball (c x) ρ', ‖w - a‖ < ρ := by
    intro w hw
    have h1 : ‖w - c x‖ < ρ' := by
      have h := Metric.mem_ball.mp hw
      rwa [dist_eq_norm] at h
    have h2 : ‖w - a‖ ≤ ‖w - c x‖ + ‖c x - a‖ := by
      calc ‖w - a‖ = ‖(w - c x) + (c x - a)‖ := by congr 1; ring
        _ ≤ ‖w - c x‖ + ‖c x - a‖ := norm_add_le _ _
    linarith
  have hformula : ∀ w ∈ Metric.ball (c x) ρ',
      chartBallBarrier c a ρ (c.symm w) = (ρ - ‖w - a‖) / ρ := by
    intro w hw
    have hwtgt : w ∈ c.target := htgt hw
    have hwsrc : c.symm w ∈ c.source := c.map_target hwtgt
    rw [chartBallBarrier_of_mem_source hwsrc, c.right_inv hwtgt, max_eq_right]
    exact div_nonneg (sub_nonneg.mpr (hlt w hw).le) hρ.le
  refine ⟨hxsrc, ρ', hρ', htgt, ?_, ?_⟩
  · have hρc : ContinuousOn (fun _ : ℂ => ρ) (Metric.ball (c x) ρ') := continuousOn_const
    have hnorm' : ContinuousOn (fun w : ℂ => ‖w - a‖) (Metric.ball (c x) ρ') :=
      (continuous_id.sub continuous_const).norm.continuousOn
    have hcont : ContinuousOn (fun w : ℂ => (ρ - ‖w - a‖) / ρ) (Metric.ball (c x) ρ') :=
      (hρc.sub hnorm').div_const ρ
    exact hcont.congr (fun w hw => hformula w hw)
  · intro p hp r hr hpr
    have havg : Real.circleAverage (fun w : ℂ => chartBallBarrier c a ρ (c.symm w)) p r
        = Real.circleAverage (fun w : ℂ => (ρ - ‖w - a‖) / ρ) p r :=
      Real.circleAverage_congr_sphere (f₁ := fun w : ℂ => chartBallBarrier c a ρ (c.symm w))
        (f₂ := fun w : ℂ => (ρ - ‖w - a‖) / ρ) (by
          intro w hw
          refine hformula w (hpr (Metric.sphere_subset_closedBall ?_))
          rwa [abs_of_pos hr] at hw)
    change Real.circleAverage (fun w : ℂ => chartBallBarrier c a ρ (c.symm w)) p r
      ≤ chartBallBarrier c a ρ (c.symm p)
    rw [havg, hformula p hp]
    have hmvp : ‖p - a‖ ≤ Real.circleAverage (fun w : ℂ => ‖w - a‖) p r :=
      Commons.Analysis.Complex.Analytic.norm_le_circleAverage (Ω := univ) isOpen_univ
        (fun z _ => analyticAt_id.sub analyticAt_const) p (mem_univ p) r hr (subset_univ _)
    have hint : CircleIntegrable (fun w : ℂ => ‖w - a‖) p r :=
      ((continuous_id.sub continuous_const).norm.continuousOn).circleIntegrable'
    have key : Real.circleAverage (fun w : ℂ => (ρ - ‖w - a‖) / ρ) p r
        = (1 / ρ) * (ρ - Real.circleAverage (fun w : ℂ => ‖w - a‖) p r) := by
      have hcongr : (fun w : ℂ => (ρ - ‖w - a‖) / ρ)
          = fun w : ℂ => (1 / ρ) • (ρ - ‖w - a‖) := by
        funext w
        rw [smul_eq_mul, div_eq_inv_mul, one_div]
      rw [hcongr, Real.circleAverage_fun_smul,
        Real.circleAverage_fun_sub (circleIntegrable_const ρ p r) hint,
        Real.circleAverage_const]
      rfl
    calc Real.circleAverage (fun w : ℂ => (ρ - ‖w - a‖) / ρ) p r
        = (1 / ρ) * (ρ - Real.circleAverage (fun w : ℂ => ‖w - a‖) p r) := key
      _ ≤ (1 / ρ) * (ρ - ‖p - a‖) := by
          refine mul_le_mul_of_nonneg_left (by linarith [hmvp]) ?_
          positivity
      _ = (ρ - ‖p - a‖) / ρ := by rw [div_eq_inv_mul]; ring

/-- **The barrier is superharmonic at each point of the chart ball, in the preferred chart at that
point.**  This is `superharmonicAtChart_chartBallBarrier` transported across the analytic chart
transition. -/
theorem superharmonicOnXAt_chartBallBarrier {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hc : c ∈ atlas ℂ X) (hρ : 0 < ρ) {x : X} (hx : x ∈ chartBall c a ρ) :
    SuperharmonicOnXAt (chartBallBarrier c a ρ) x :=
  SuperharmonicAtChart.transport (u := chartBallBarrier c a ρ) (c := c) (d := chartAt ℂ x)
    hx.1 (mem_chart_source ℂ x)
    (analyticAt_transition_of_mem_atlas hc (chart_mem_atlas ℂ x))
    (analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x) hc)
    (superharmonicAtChart_chartBallBarrier c a hρ hx)

/-- **The chart-ball barrier is superharmonic on the chart ball.** -/
theorem superharmonicOnX_chartBallBarrier {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hc : c ∈ atlas ℂ X) (hρ : 0 < ρ) :
    SuperharmonicOnX (chartBallBarrier c a ρ) (chartBall c a ρ) :=
  ⟨continuousOn_chartBallBarrier c a hρ,
    fun x hx => superharmonicOnXAt_chartBallBarrier hc hρ hx⟩

end Barrier

end Submission
