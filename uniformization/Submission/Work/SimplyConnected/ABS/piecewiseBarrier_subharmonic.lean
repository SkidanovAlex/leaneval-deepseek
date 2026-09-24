import Mathlib
import Submission.Work.SimplyConnected.ABS.MajorantBarrierDefs
import Submission.Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts
import Submission.Work.SimplyConnected.ABS.dirichletSphereEnvelope_outerGap

/-!
# The piecewise barrier of the superharmonic-majorant construction is subharmonic

Hubbard, *Teichmüller theory* Vol. 1, and Anghel–Bruin–Stan, *Uniformization of Riemann surfaces
revisited* (arXiv:2008.12189), Proposition 9.

The piecewise barrier `Submission.piecewiseBarrier c a ρ s A B h₁` is

* the logarithmic potential `log ‖c x - a‖ - A` on the closed chart disc `chartClosedBall c a s`,
* the pointwise maximum `max (log ‖c x - a‖ - A) (-B * h₁ x)` on the annulus
  `chartBall c a ρ \ chartClosedBall c a s`,
* `-B * h₁ x` outside the chart ball `chartBall c a ρ`.

The theorem below collects the four properties of that function that the balayage (sweep)
construction uses:

1. it is **subharmonic** on `Ω \ {x₀}` (`piecewiseBarrier_subharmonic`),
2. it is **dominated by** `- chartLogClamp c a ρ`, hence by the negative of the chart-disc Green
   function,
3. it **dominates** the `h₁`-branch `-B * h₁` off the closed chart disc, and
4. on the closed chart disc it is **exactly** the logarithmic potential `log ‖c x - a‖ - A`.

Everything is proved here, together with the auxiliary facts about `chartLogPotential` (the
clamped logarithmic potential) that the local analysis of the piecewise function needs.

The proof of subharmonicity is a local case analysis at a point `x ∈ Ω \ {x₀}`, according to the
position of `‖c x - a‖` relative to `s` and `ρ`:

* strictly inside the chart disc `chartClosedBall c a s`, and on its boundary, the barrier agrees
  with the harmonic logarithmic potential near `x` — this is the only place where the hypotheses
  on `h₁` are used at an inner boundary point, via `h₁ ≥ log (ρ/‖c x - a‖) / log (ρ/s) → 1`, which
  shows that the branch `-B h₁` is dominated by the potential near the inner sphere;
* on the annulus the barrier agrees with the maximum of two functions harmonic near `x` (the
  potential, and the harmonic function `-B h₁`, which is harmonic there by `h1harm`);
* on the outer sphere `‖c x - a‖ = ρ` and outside the chart ball, the barrier agrees with `-B h₁`
  near `x`, since at the outer sphere the `h₁`-branch wins by `hθ` and `hB3`.

Since the notion of subharmonicity `Submission.SubharmonicOnXAt` is expressed in the preferred
chart at the base point, the statements about the chart `c` are transported across the analytic
chart transition (`Submission.SubharmonicAtChart.transport`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## Elementary facts about the chart balls and the barrier -/

/-- A closed chart disc of radius `s` is contained in the open chart disc of any larger radius. -/
theorem chartClosedBall_subset_chartBall_of_lt {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {s ρ : ℝ}
    (hsρ : s < ρ) : Submission.chartClosedBall c a s ⊆ Submission.chartBall c a ρ := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  show c x ∈ Metric.ball a ρ
  have h := Metric.mem_closedBall.mp hx.2
  rw [dist_eq_norm] at h
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt h hsρ

/-- Outside the chart ball, the piecewise barrier is the `h₁`-branch `-B * h₁`. -/
theorem piecewiseBarrier_of_not_mem_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ s A B : ℝ} {h₁ : X → ℝ} {x : X} (hsρ : s < ρ)
    (hx : x ∉ Submission.chartBall c a ρ) :
    Submission.piecewiseBarrier c a ρ s A B h₁ x = -B * h₁ x := by
  have hx' : x ∉ Submission.chartClosedBall c a s :=
    fun h => hx (chartClosedBall_subset_chartBall_of_lt hsρ h)
  rw [Submission.piecewiseBarrier, if_neg hx', if_neg hx]

/-- The clamped logarithmic potential is bounded above by the constant `log ρ - A` away from the
pole of the chart. -/
theorem chartLogPotential_le_log_rho_sub_A {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ A : ℝ}
    {x : X} (hne : c x ≠ a) :
    Submission.chartLogPotential c a ρ A x ≤ Real.log ρ - A := by
  by_cases hx : x ∈ Submission.chartBall c a ρ
  · rw [Submission.chartLogPotential_of_mem hx]
    have hpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hlt : ‖c x - a‖ < ρ := by
      have h := Metric.mem_ball.mp hx.2; rwa [dist_eq_norm] at h
    linarith [Real.log_lt_log hpos hlt]
  · rw [Submission.chartLogPotential_of_not_mem hx]

/-! ## Local analysis of the clamped logarithmic potential -/

/-- Near a point `x` of the source of the chart at which the logarithmic potential is finite, the
chart pullback of `Submission.chartLogPotential c a ρ A` agrees with the model function
`w ↦ log ‖w - a‖ - A` on a ball around `c x` which is contained in the target of the chart and on
which the pole `a` does not appear and the potential is unclamped. -/
theorem chartLogPotential_local {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ A : ℝ} {x : X}
    (hxsrc : x ∈ c.source) (hxne : c x ≠ a) (hxball : ‖c x - a‖ < ρ) :
    ∃ η : ℝ, 0 < η ∧ Metric.ball (c x) η ⊆ c.target ∧
      (∀ w ∈ Metric.ball (c x) η, w ≠ a) ∧
      (∀ w ∈ Metric.ball (c x) η, ‖w - a‖ < ρ) ∧
      (∀ w ∈ Metric.ball (c x) η,
        (Submission.chartLogPotential c a ρ A ∘ c.symm) w = Real.log ‖w - a‖ - A) := by
  have hpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hxsrc))
  have hkey : ∀ w ∈ Metric.ball (c x) (min (min δ (ρ - ‖c x - a‖)) ‖c x - a‖),
      ‖w - c x‖ < min (min δ (ρ - ‖c x - a‖)) ‖c x - a‖ := by
    intro w hw
    have h := Metric.mem_ball.mp hw
    rwa [dist_eq_norm] at h
  refine ⟨min (min δ (ρ - ‖c x - a‖)) ‖c x - a‖,
    lt_min (lt_min hδ (by linarith)) hpos, ?_, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))).trans hδsub
  · intro w hw
    have h1' : ‖w - c x‖ < ‖c x - a‖ := lt_of_lt_of_le (hkey w hw) (min_le_right _ _)
    have h2 : ‖c x - a‖ ≤ ‖c x - w‖ + ‖w - a‖ := by
      calc ‖c x - a‖ = ‖(c x - w) + (w - a)‖ := by congr 1; ring
        _ ≤ ‖c x - w‖ + ‖w - a‖ := norm_add_le _ _
    rw [norm_sub_rev (c x) w] at h2
    have h3 : 0 < ‖w - a‖ := by linarith
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt h3))
  · intro w hw
    have h1' : ‖w - c x‖ < ρ - ‖c x - a‖ :=
      lt_of_lt_of_le (hkey w hw) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h4 : ‖w - a‖ ≤ ‖w - c x‖ + ‖c x - a‖ := by
      calc ‖w - a‖ = ‖(w - c x) + (c x - a)‖ := by congr 1; ring
        _ ≤ ‖w - c x‖ + ‖c x - a‖ := norm_add_le _ _
    linarith
  · intro w hw
    have h1 : ‖w - c x‖ < min (min δ (ρ - ‖c x - a‖)) ‖c x - a‖ := hkey w hw
    have h2 : ‖w - c x‖ < δ := lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_left _ _))
    have hwtgt : w ∈ c.target := hδsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact h2))
    have hwsrc : c.symm w ∈ c.source := c.map_target hwtgt
    have hlt : ‖w - a‖ < ρ := by
      have h4 : ‖w - a‖ ≤ ‖w - c x‖ + ‖c x - a‖ := by
        calc ‖w - a‖ = ‖(w - c x) + (c x - a)‖ := by congr 1; ring
          _ ≤ ‖w - c x‖ + ‖c x - a‖ := norm_add_le _ _
      have h5 : ‖w - c x‖ < ρ - ‖c x - a‖ :=
        lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_right _ _))
      linarith
    have hmem : c.symm w ∈ Submission.chartBall c a ρ := by
      refine ⟨hwsrc, ?_⟩
      show c (c.symm w) ∈ Metric.ball a ρ
      rw [c.right_inv hwtgt, Metric.mem_ball, dist_eq_norm]
      exact hlt
    simp only [Function.comp_apply]
    rw [Submission.chartLogPotential_of_mem hmem, c.right_inv hwtgt]

/-- The chart pullback of the clamped logarithmic potential is harmonic where the potential is
unclamped and finite. -/
theorem harmonicAt_chartLogPotential_comp {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ A : ℝ}
    {x : X} (hxsrc : x ∈ c.source) (hxne : c x ≠ a) (hxball : ‖c x - a‖ < ρ) :
    InnerProductSpace.HarmonicAt (Submission.chartLogPotential c a ρ A ∘ c.symm) (c x) := by
  obtain ⟨η, hη, -, -, -, heq⟩ := chartLogPotential_local hxsrc hxne hxball
  refine (InnerProductSpace.harmonicAt_congr_nhds
    (f₁ := Submission.chartLogPotential c a ρ A ∘ c.symm)
    (f₂ := fun w : ℂ => Real.log ‖w - a‖ - A) ?_).mpr ?_
  · filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hη)] with w hw
    exact heq w hw
  · exact (Submission.harmonicAt_log_norm_sub hxne).sub (InnerProductSpace.harmonicAt_const A)

/-- A function whose chart pullback is harmonic on a ball is subharmonic at the centre of the ball
(Hubbard's Definition 1.2.1, expressed in the chart `c`). -/
theorem SubharmonicAtChart_of_harmonicAt {c : OpenPartialHomeomorph X ℂ} {u : X → ℝ} {x : X}
    {η : ℝ} (hx : x ∈ c.source) (hη : 0 < η) (htgt : Metric.ball (c x) η ⊆ c.target)
    (hharm : ∀ z ∈ Metric.ball (c x) η, InnerProductSpace.HarmonicAt (u ∘ c.symm) z) :
    Submission.SubharmonicAtChart u c x := by
  refine ⟨hx, η, hη, htgt, ?_, ?_⟩
  · exact continuousOn_of_forall_continuousAt (fun z hz => (hharm z hz).1.continuousAt)
  · intro p hp r hr hpr
    have hh : InnerProductSpace.HarmonicOnNhd (u ∘ c.symm) (Metric.closedBall p |r|) := by
      rw [abs_of_pos hr]
      exact fun z hz => hharm z (hpr hz)
    exact (InnerProductSpace.HarmonicOnNhd.circleAverage_eq hh).ge

/-- **The clamped logarithmic potential is subharmonic at every point at which it is finite**, in
the sense of the preferred chart at that point. -/
theorem subharmonicOnXAt_chartLogPotential {c : OpenPartialHomeomorph X ℂ}
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hc : c ∈ atlas ℂ X) {a : ℂ} {ρ A : ℝ} {x : X} (hxsrc : x ∈ c.source)
    (hxne : c x ≠ a) (hxball : ‖c x - a‖ < ρ) :
    Submission.SubharmonicOnXAt (Submission.chartLogPotential c a ρ A) x := by
  obtain ⟨η, hη, htgt, hne, -, heq⟩ := chartLogPotential_local hxsrc hxne hxball
  have hchart : Submission.SubharmonicAtChart (Submission.chartLogPotential c a ρ A) c x := by
    refine SubharmonicAtChart_of_harmonicAt hxsrc hη htgt (fun z hz => ?_)
    refine (InnerProductSpace.harmonicAt_congr_nhds
      (f₁ := Submission.chartLogPotential c a ρ A ∘ c.symm)
      (f₂ := fun w : ℂ => Real.log ‖w - a‖ - A) ?_).mpr ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact heq w hw
    · exact (Submission.harmonicAt_log_norm_sub (hne z hz)).sub
        (InnerProductSpace.harmonicAt_const A)
  exact Submission.SubharmonicAtChart.transport (u := Submission.chartLogPotential c a ρ A)
    (c := c) (d := chartAt ℂ x) hxsrc (mem_chart_source ℂ x)
    (Submission.analyticAt_transition_of_mem_atlas hc (chart_mem_atlas ℂ x))
    (Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x) hc) hchart

/-- A positive multiple of a function harmonic at a point is subharmonic there. -/
theorem subharmonicOnXAt_negB_mul {u : X → ℝ} {B : ℝ} {x : X}
    (hu : Submission.HarmonicOnXAt u x) :
    Submission.SubharmonicOnXAt (fun y => -B * u y) x := by
  have h1 : Submission.HarmonicOnXAt ((-B) • u) x := hu.const_smul (-B)
  have h2 : Submission.SubharmonicOnXAt ((-B) • u) x := h1.subharmonic
  refine Submission.SubharmonicOnXAt.congr h2 (Filter.Eventually.of_forall (fun y => ?_))
  simp only [Pi.smul_apply, smul_eq_mul]


/-! ## The inner-sphere computation -/

/-- Near the inner chart sphere, the `h₁`-branch `-B * h₁` of the barrier is dominated by the
logarithmic branch `chartLogPotential c a ρ A`.  This is the only place where the asymptotic
hypotheses `h1lb` (the lower bound for `h₁` at the inner sphere) and `hB2` are used. -/
theorem eventually_negB_mul_le_chartLogPotential {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ s A B : ℝ} {h₁ : X → ℝ} {Ω : Set X}
    (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ) (hB : 0 < B)
    (hB2 : A - Real.log s < B)
    (hρΩ : Submission.chartClosedBall c a ρ ⊆ Ω)
    (h1lb : ∀ y ∈ (Ω \ Submission.chartClosedBall c a s),
      Submission.chartLogClamp c a ρ y ≤ Real.log (ρ / s) * h₁ y)
    {x : X} (hxsrc : x ∈ c.source) (hxs : ‖c x - a‖ = s) :
    ∀ᶠ y in 𝓝 x, y ∈ c.source → s < ‖c y - a‖ → ‖c y - a‖ < ρ →
      -B * h₁ y ≤ Submission.chartLogPotential c a ρ A y := by
  have hlogpos : 0 < Real.log (ρ / s) := Real.log_pos (by rw [one_lt_div hs]; exact hsρ)
  have hsne : s ≠ 0 := hs.ne'
  have hΦΨ : -B * (Real.log (ρ / s) / Real.log (ρ / s)) < Real.log s - A := by
    rw [div_self hlogpos.ne', mul_one]
    linarith
  have hcontΦ : ContinuousAt (fun t : ℝ => -B * (Real.log (ρ / t) / Real.log (ρ / s))) s := by
    have h1 : ContinuousAt (fun t : ℝ => ρ / t) s :=
      continuousAt_const.div continuousAt_id hsne
    have h2 : ContinuousAt (fun t : ℝ => Real.log (ρ / t)) s :=
      h1.log (div_ne_zero hρ.ne' hsne)
    have h3 : ContinuousAt (fun t : ℝ => Real.log (ρ / t) / Real.log (ρ / s)) s :=
      h2.div continuousAt_const hlogpos.ne'
    simpa using h3.const_mul (-B)
  have hcontΨ : ContinuousAt (fun t : ℝ => Real.log t - A) s :=
    (continuousAt_id.log hsne).sub continuousAt_const
  have hscalar : ∀ᶠ t in 𝓝 s,
      -B * (Real.log (ρ / t) / Real.log (ρ / s)) ≤ Real.log t - A :=
    (hcontΦ.eventually_lt hcontΨ hΦΨ).mono (fun t ht => ht.le)
  have htend : Filter.Tendsto (fun y : X => ‖c y - a‖) (𝓝 x) (𝓝 s) := by
    have hcont : ContinuousAt (fun y : X => ‖c y - a‖) x :=
      ((c.continuousAt hxsrc).sub continuousAt_const).norm
    have h := ContinuousAt.tendsto hcont
    rwa [hxs] at h
  have h1ev := htend.eventually hscalar
  have hlt_ev : ∀ᶠ y in 𝓝 x, ‖c y - a‖ < ρ :=
    htend.eventually_lt tendsto_const_nhds hsρ
  filter_upwards [h1ev, c.open_source.mem_nhds hxsrc, hlt_ev] with y hsc hysrc hyltρ
  intro _ hgts _
  have hyρ : y ∈ Submission.chartBall c a ρ := by
    refine ⟨hysrc, ?_⟩
    show c y ∈ Metric.ball a ρ
    rw [Metric.mem_ball, dist_eq_norm]
    exact hyltρ
  have hycB : y ∉ Submission.chartClosedBall c a s := by
    intro h
    have h2 := Metric.mem_closedBall.mp h.2
    rw [dist_eq_norm] at h2
    linarith
  have hylb := h1lb y ⟨hρΩ (Submission.chartBall_subset_chartClosedBall c a ρ hyρ), hycB⟩
  rw [Submission.chartLogClamp_of_mem hyρ] at hylb
  have hge : Real.log (ρ / ‖c y - a‖) / Real.log (ρ / s) ≤ h₁ y := by
    rw [div_le_iff₀ hlogpos]
    linarith
  have hchain : -B * h₁ y ≤ -B * (Real.log (ρ / ‖c y - a‖) / Real.log (ρ / s)) :=
    mul_le_mul_of_nonpos_left hge (by linarith)
  rw [Submission.chartLogPotential_of_mem hyρ]
  linarith [hchain, hsc]

/-! ## The barrier: subharmonicity, domination, and the inner value -/

/-- **The four properties of the piecewise barrier.**  This is the general form of
`Work.SimplyConnected.ABS.piecewiseBarrier_subharmonic`, stated for an arbitrary chart `c` of the
atlas and an arbitrary centre `a` (with the pole of the barrier at the point `x₀` of the source
mapping to `a`), so that the proof may work in the coordinates of `c` throughout. -/
theorem piecewiseBarrier_subharmonic_of_chart {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {a : ℂ}
    {Ω : Set X} {x₀ : X} (hx₀c : c x₀ = a) (hx₀src : x₀ ∈ c.source)
    {ρ s A B : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall a ρ ⊆ c.target)
    (hρΩ : Submission.chartClosedBall c a ρ ⊆ Ω)
    {h₁ : X → ℝ}
    (hA : Real.log ρ ≤ A) (hB : 0 < B) (hB1 : Real.log (ρ / s) ≤ B) (hB2 : A - Real.log s < B)
    (h1harm : Submission.HarmonicOnX h₁ (Ω \ Submission.chartClosedBall c a s))
    (h1nonneg : ∀ x : X, 0 ≤ h₁ x) (h1le : ∀ x : X, h₁ x ≤ 1)
    (h1lb : ∀ x ∈ (Ω \ Submission.chartClosedBall c a s),
      Submission.chartLogClamp c a ρ x ≤ Real.log (ρ / s) * h₁ x)
    (h1lim : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ (Ω \ Submission.chartClosedBall c a s),
        x ∈ c.source → ‖c x - a‖ < s + δ → 1 - ε ≤ h₁ x)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 1 - θ ≥ 0)
    (hθ : ∀ x ∈ (Ω \ Submission.chartClosedBall c a s),
        x ∈ c.source → ‖c x - a‖ = ρ → h₁ x ≤ 1 - θ)
    (hB3 : B * (1 - θ) < A - Real.log ρ) :
    Submission.SubharmonicOnX
        (Submission.piecewiseBarrier c a ρ s A B h₁) (Ω \ {x₀}) ∧
      (∀ x ∈ Ω \ {x₀}, Submission.piecewiseBarrier c a ρ s A B h₁ x
        ≤ - Submission.chartLogClamp c a ρ x) ∧
      (∀ x ∈ Ω \ {x₀}, x ∉ Submission.chartClosedBall c a s →
        -B * h₁ x ≤ Submission.piecewiseBarrier c a ρ s A B h₁ x) ∧
      (∀ x ∈ Ω \ {x₀}, x ∈ Submission.chartClosedBall c a s →
        Submission.piecewiseBarrier c a ρ s A B h₁ x = Real.log ‖c x - a‖ - A) := by
  -- the value on the closed chart disc
  have hinner : ∀ x ∈ Ω \ {x₀}, x ∈ Submission.chartClosedBall c a s →
      Submission.piecewiseBarrier c a ρ s A B h₁ x = Real.log ‖c x - a‖ - A := by
    intro x _ hx
    have hxρ : x ∈ Submission.chartBall c a ρ := chartClosedBall_subset_chartBall_of_lt hsρ hx
    rw [Submission.piecewiseBarrier_of_mem_inner hx, Submission.chartLogPotential_of_mem hxρ]
  -- the domination of the `h₁`-branch off the closed chart disc
  have hge : ∀ x ∈ Ω \ {x₀}, x ∉ Submission.chartClosedBall c a s →
      -B * h₁ x ≤ Submission.piecewiseBarrier c a ρ s A B h₁ x := by
    intro x _ hx
    by_cases hxρ : x ∈ Submission.chartBall c a ρ
    · rw [Submission.piecewiseBarrier_of_mem_middle hx hxρ]
      exact le_max_right _ _
    · rw [piecewiseBarrier_of_not_mem_chartBall hsρ hxρ]
  -- the domination of the negative clamped logarithmic potential
  have hle : ∀ x ∈ Ω \ {x₀}, Submission.piecewiseBarrier c a ρ s A B h₁ x
      ≤ - Submission.chartLogClamp c a ρ x := by
    intro x hxU
    have hxne : x ≠ x₀ := by simpa using hxU.2
    by_cases hxcB : x ∈ Submission.chartClosedBall c a s
    · have hxρ : x ∈ Submission.chartBall c a ρ := chartClosedBall_subset_chartBall_of_lt hsρ hxcB
      have hcx : c x ≠ a := fun h => hxne (c.injOn hxcB.1 hx₀src (by rw [h, hx₀c]))
      have hnormpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcx)
      have hlt : ‖c x - a‖ < ρ := by
        have h := Metric.mem_ball.mp hxρ.2
        rwa [dist_eq_norm] at h
      rw [hinner x hxU hxcB, Submission.chartLogClamp_of_mem hxρ,
        Real.log_div hρ.ne' (ne_of_gt hnormpos)]
      linarith [Real.log_lt_log hnormpos hlt]
    · by_cases hxρ : x ∈ Submission.chartBall c a ρ
      · have hcx : c x ≠ a := fun h => hxne (c.injOn hxρ.1 hx₀src (by rw [h, hx₀c]))
        have hnormpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcx)
        have hlt : ‖c x - a‖ < ρ := by
          have h := Metric.mem_ball.mp hxρ.2
          rwa [dist_eq_norm] at h
        rw [Submission.piecewiseBarrier_of_mem_middle hxcB hxρ]
        refine max_le ?_ ?_
        · rw [Submission.chartLogPotential_of_mem hxρ, Submission.chartLogClamp_of_mem hxρ,
            Real.log_div hρ.ne' (ne_of_gt hnormpos)]
          linarith [Real.log_lt_log hnormpos hlt]
        · have hlb := h1lb x ⟨hxU.1, hxcB⟩
          rw [Submission.chartLogClamp_of_mem hxρ] at hlb
          rw [Submission.chartLogClamp_of_mem hxρ]
          nlinarith [hlb, h1nonneg x, hB1]
      · rw [piecewiseBarrier_of_not_mem_chartBall hsρ hxρ,
          Submission.chartLogClamp_of_not_mem hxρ]
        nlinarith [h1nonneg x, hB]
  -- subharmonicity: a local case analysis
  have hsub_at : ∀ x ∈ Ω \ {x₀},
      Submission.SubharmonicOnXAt (Submission.piecewiseBarrier c a ρ s A B h₁) x := by
    intro x hxU
    have hxΩ : x ∈ Ω := hxU.1
    have hxne : x ≠ x₀ := by simpa using hxU.2
    have hcB_of_norm : ∀ y : X, s < ‖c y - a‖ → y ∉ Submission.chartClosedBall c a s := by
      intro y hy h
      have h2 := Metric.mem_closedBall.mp h.2
      rw [dist_eq_norm] at h2
      linarith
    by_cases hxsrc : x ∈ c.source
    · have hcx : c x ≠ a := fun h => hxne (c.injOn hxsrc hx₀src (by rw [h, hx₀c]))
      have hxcB_of_norm : ∀ x' : X, s < ‖c x' - a‖ → x' ∉ Submission.chartClosedBall c a s :=
        fun x' h => hcB_of_norm x' h
      have htend : Filter.Tendsto (fun y : X => ‖c y - a‖) (𝓝 x) (𝓝 ‖c x - a‖) := by
        have hcont : ContinuousAt (fun y : X => ‖c y - a‖) x :=
          ((c.continuousAt hxsrc).sub continuousAt_const).norm
        exact ContinuousAt.tendsto hcont
      rcases lt_trichotomy ‖c x - a‖ s with hlt | heq | hgt
      · -- strictly inside the inner disc: the barrier is the logarithmic potential
        have hxρ : ‖c x - a‖ < ρ := by linarith
        have hmemb : x ∈ Submission.chartBall c a s := by
          refine ⟨hxsrc, ?_⟩
          show c x ∈ Metric.ball a s
          rw [Metric.mem_ball, dist_eq_norm]
          exact hlt
        have hev : Submission.piecewiseBarrier c a ρ s A B h₁
            =ᶠ[𝓝 x] Submission.chartLogPotential c a ρ A := by
          filter_upwards [(Submission.chartBall_isOpen c a s).mem_nhds hmemb] with y hy
          exact Submission.piecewiseBarrier_of_mem_inner
            (Submission.chartBall_subset_chartClosedBall c a s hy)
        exact Submission.SubharmonicOnXAt.congr
          (subharmonicOnXAt_chartLogPotential hc hxsrc hcx hxρ) hev.symm
      · -- on the inner sphere: the logarithmic potential still wins
        have hxρ : ‖c x - a‖ < ρ := by rw [heq]; exact hsρ
        have h1ev := eventually_negB_mul_le_chartLogPotential (c := c) (a := a) (Ω := Ω)
          hρ hs hsρ hB hB2 hρΩ h1lb hxsrc heq
        have hsrc_ev : ∀ᶠ y in 𝓝 x, y ∈ c.source := c.open_source.mem_nhds hxsrc
        have hlt_ev : ∀ᶠ y in 𝓝 x, ‖c y - a‖ < ρ :=
          htend.eventually_lt tendsto_const_nhds (by rw [heq]; exact hsρ)
        have hev : Submission.piecewiseBarrier c a ρ s A B h₁
            =ᶠ[𝓝 x] Submission.chartLogPotential c a ρ A := by
          filter_upwards [h1ev, hsrc_ev, hlt_ev] with y hyv hysrc hyltρ
          by_cases hycB : y ∈ Submission.chartClosedBall c a s
          · exact Submission.piecewiseBarrier_of_mem_inner hycB
          · have hyρ : y ∈ Submission.chartBall c a ρ := by
              refine ⟨hysrc, ?_⟩
              show c y ∈ Metric.ball a ρ
              rw [Metric.mem_ball, dist_eq_norm]
              exact hyltρ
            have hys : s < ‖c y - a‖ := by
              rcases lt_or_ge s ‖c y - a‖ with h | h
              · exact h
              · exact absurd (show y ∈ Submission.chartClosedBall c a s from
                  ⟨hysrc, by
                    show c y ∈ Metric.closedBall a s
                    rw [Metric.mem_closedBall, dist_eq_norm]
                    exact h⟩) hycB
            rw [Submission.piecewiseBarrier_of_mem_middle hycB hyρ,
              max_eq_left (hyv hysrc hys hyltρ)]
        exact Submission.SubharmonicOnXAt.congr
          (subharmonicOnXAt_chartLogPotential hc hxsrc hcx hxρ) hev.symm
      · -- in the annulus, and beyond: split on the outer radius
        rcases lt_trichotomy ‖c x - a‖ ρ with hρlt | hρeq | hρgt
        · -- the annulus: maximum of two functions harmonic near `x`
          have hxρ : ‖c x - a‖ < ρ := hρlt
          have hxcB : x ∉ Submission.chartClosedBall c a s := hcB_of_norm x hgt
          have hu : Submission.SubharmonicOnXAt (Submission.chartLogPotential c a ρ A) x :=
            subharmonicOnXAt_chartLogPotential hc hxsrc hcx hxρ
          have hv : Submission.SubharmonicOnXAt (fun y => -B * h₁ y) x :=
            subharmonicOnXAt_negB_mul ((h1harm x ⟨hxΩ, hxcB⟩))
          have hsup := hu.sup hv
          refine Submission.SubharmonicOnXAt.congr hsup ?_
          have hsrc_ev : ∀ᶠ y in 𝓝 x, y ∈ c.source := c.open_source.mem_nhds hxsrc
          have hgts_ev : ∀ᶠ y in 𝓝 x, s < ‖c y - a‖ :=
            tendsto_const_nhds.eventually_lt htend hgt
          have hltρ_ev : ∀ᶠ y in 𝓝 x, ‖c y - a‖ < ρ :=
            htend.eventually_lt tendsto_const_nhds hρlt
          filter_upwards [hsrc_ev, hgts_ev, hltρ_ev] with y hysrc hys hylt
          have hyρ : y ∈ Submission.chartBall c a ρ := by
            refine ⟨hysrc, ?_⟩
            show c y ∈ Metric.ball a ρ
            rw [Metric.mem_ball, dist_eq_norm]
            exact hylt
          exact (Submission.piecewiseBarrier_of_mem_middle (hcB_of_norm y hys) hyρ).symm
        · -- on the outer sphere: the `h₁`-branch wins
          have hxcB : x ∉ Submission.chartClosedBall c a s := by
            intro h
            have h2 := Metric.mem_closedBall.mp h.2
            rw [dist_eq_norm] at h2
            linarith [hgt]
          have hv : Submission.SubharmonicOnXAt (fun y => -B * h₁ y) x :=
            subharmonicOnXAt_negB_mul (h1harm x ⟨hxΩ, hxcB⟩)
          have hθx : h₁ x ≤ 1 - θ := hθ x ⟨hxΩ, hxcB⟩ hxsrc hρeq
          have hvx : Real.log ρ - A < -B * h₁ x := by
            have h1 : -B * (1 - θ) ≤ -B * h₁ x :=
              mul_le_mul_of_nonpos_left hθx (by linarith)
            linarith
          have hv_ev : ∀ᶠ y in 𝓝 x, Real.log ρ - A < -B * h₁ y :=
            continuousAt_const.eventually_lt
              ((h1harm x ⟨hxΩ, hxcB⟩).continuousAt.const_mul (-B)) hvx
          have hgts_ev : ∀ᶠ y in 𝓝 x, s < ‖c y - a‖ :=
            tendsto_const_nhds.eventually_lt htend (by rw [hρeq]; exact hsρ)
          refine Submission.SubharmonicOnXAt.congr hv ?_
          filter_upwards [hv_ev, hgts_ev] with y hyv hygt
          have hyne : c y ≠ a := by
            intro h
            rw [h, sub_self, norm_zero] at hygt
            linarith
          by_cases hyρ : y ∈ Submission.chartBall c a ρ
          · rw [Submission.piecewiseBarrier_of_mem_middle (hcB_of_norm y hygt) hyρ,
              max_eq_right (le_of_lt (lt_of_le_of_lt (chartLogPotential_le_log_rho_sub_A hyne) hyv))]
          · rw [piecewiseBarrier_of_not_mem_chartBall hsρ hyρ]
        · -- outside the chart ball: the barrier is the `h₁`-branch
          have hxcB : x ∉ Submission.chartClosedBall c a s := by
            intro h
            have h2 := Metric.mem_closedBall.mp h.2
            rw [dist_eq_norm] at h2
            linarith [hgt]
          have hv : Submission.SubharmonicOnXAt (fun y => -B * h₁ y) x :=
            subharmonicOnXAt_negB_mul (h1harm x ⟨hxΩ, hxcB⟩)
          refine Submission.SubharmonicOnXAt.congr hv ?_
          have hltρ : ‖c x - a‖ > ρ := hρgt
          have hgtρ_ev : ∀ᶠ y in 𝓝 x, ρ < ‖c y - a‖ :=
            tendsto_const_nhds.eventually_lt htend hρgt
          filter_upwards [hgtρ_ev] with y hygt
          rw [piecewiseBarrier_of_not_mem_chartBall hsρ (fun h => by
            have h2 := Metric.mem_ball.mp h.2
            rw [dist_eq_norm] at h2
            linarith)]
    · -- outside the source of the chart: the barrier is the `h₁`-branch
      have hxcB : x ∉ Submission.chartClosedBall c a s :=
        fun h => hxsrc (Submission.chartClosedBall_subset_source c a s h)
      have hv : Submission.SubharmonicOnXAt (fun y => -B * h₁ y) x :=
        subharmonicOnXAt_negB_mul (h1harm x ⟨hxΩ, hxcB⟩)
      refine Submission.SubharmonicOnXAt.congr hv ?_
      have hxnotF : x ∉ Submission.chartClosedBall c a ρ :=
        fun h => hxsrc (Submission.chartClosedBall_subset_source c a ρ h)
      have hcompl : (Submission.chartClosedBall c a ρ)ᶜ ∈ 𝓝 x :=
        (Submission.isClosed_chartClosedBall hρsub).isOpen_compl.mem_nhds hxnotF
      filter_upwards [hcompl] with y hy
      rw [piecewiseBarrier_of_not_mem_chartBall hsρ
        (fun h => hy (Submission.chartBall_subset_chartClosedBall c a ρ h))]
  refine ⟨⟨continuousOn_of_forall_continuousAt (fun x hx => (hsub_at x hx).continuousAt),
    hsub_at⟩, hle, hge, hinner⟩

/-- **The piecewise barrier is subharmonic, is dominated by the negative clamped logarithmic
potential, dominates the `h₁`-branch off the closed chart disc, and equals the logarithmic
potential on the closed chart disc.** -/
theorem piecewiseBarrier_subharmonic {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {x₀ : X}
    {ρ s A B : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    {h₁ : X → ℝ}
    (hA : Real.log ρ ≤ A) (hB : 0 < B) (hB1 : Real.log (ρ / s) ≤ B)
    (hB2 : A - Real.log s < B)
    (h1harm : Submission.HarmonicOnX h₁
      (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s))
    (h1nonneg : ∀ x : X, 0 ≤ h₁ x) (h1le : ∀ x : X, h₁ x ≤ 1)
    (h1lb : ∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
      Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ x ≤ Real.log (ρ / s) * h₁ x)
    (h1lim : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
        x ∈ (chartAt ℂ x₀).source → ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ < s + δ → 1 - ε ≤ h₁ x)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 1 - θ ≥ 0)
    (hθ : ∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
        x ∈ (chartAt ℂ x₀).source → ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ = ρ → h₁ x ≤ 1 - θ)
    (hB3 : B * (1 - θ) < A - Real.log ρ) :
    Submission.SubharmonicOnX
        (Submission.piecewiseBarrier (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ s A B h₁)
        (Ω \ {x₀}) ∧
      (∀ x ∈ Ω \ {x₀}, Submission.piecewiseBarrier (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ s A B h₁ x
        ≤ - Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ x) ∧
      (∀ x ∈ Ω \ {x₀}, x ∉ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s →
        -B * h₁ x ≤
          Submission.piecewiseBarrier (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ s A B h₁ x) ∧
      (∀ x ∈ Ω \ {x₀}, x ∈ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s →
        Submission.piecewiseBarrier (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ s A B h₁ x
          = Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ - A) :=
  piecewiseBarrier_subharmonic_of_chart (X := X) (c := chartAt ℂ x₀)
    (a := (chartAt ℂ x₀) x₀) (chart_mem_atlas ℂ x₀) rfl (mem_chart_source ℂ x₀)
    hρ hs hsρ hρsub hρΩ hA hB hB1 hB2 h1harm h1nonneg h1le h1lb h1lim hθ0 hθ1 hθ hB3

end Work.SimplyConnected.ABS
