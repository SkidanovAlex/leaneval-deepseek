import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.GreenFunction
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.subMeanValue_max_const

/-!
# The clamped logarithmic potential of a chart ball

The Green-function construction of `X` with pole `z₀` uses as its *barrier* the function

`χ = log (ρ / ‖c x - a‖)` on the chart ball `chartBall c a ρ`, clamped to `0` outside,

where `c = chartAt ℂ z₀` and `a = c z₀`.  (`Submission.chartLogClamp` below.)  It is the
"Green function of the chart ball" made into a global function by the zero extension.

The two structural properties that matter are

* `χ` is **non-negative** everywhere and **subharmonic** on `univ ∖ {z₀}` (so that it may serve
  as the barrier of a balayage family, see `Submission/Sweep.lean`); the subharmonicity comes
  from the identity `χ = max (log fun, 0)` valid on the source of the chart, together with the
  fact that the maximum of a harmonic function and a constant satisfies the circle
  sub-mean-value inequality (commons `subMeanValue_max_const`);
* `χ` is **unbounded above near `z₀`** and strictly positive on a punctured neighbourhood of
  `z₀` (`chartLogClamp_pos`), which is what makes the sweep of `χ` a function with a
  logarithmic pole.

The technical care in the continuity statement is the zero extension: the values of the chart
map outside its source are unconstrained, so the definition clamps on the *set* `chartBall`,
and continuity outside the source is obtained from the compactness of
`c.symm '' Metric.closedBall a ρ ⊆ c.source`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section ChartLogClamp

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The clamped logarithmic potential of the chart ball `chartBall c a ρ`**: the logarithmic
potential `log (ρ / ‖c x - a‖)` on the chart ball, extended by `0` outside it. -/
noncomputable def chartLogClamp (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : X → ℝ :=
  fun x => if x ∈ chartBall c a ρ then Real.log (ρ / ‖c x - a‖) else 0

theorem chartLogClamp_of_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {x : X}
    (hx : x ∈ chartBall c a ρ) : chartLogClamp c a ρ x = Real.log (ρ / ‖c x - a‖) :=
  if_pos hx

theorem chartLogClamp_of_not_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {x : X}
    (hx : x ∉ chartBall c a ρ) : chartLogClamp c a ρ x = 0 := if_neg hx

/-- On the source of the chart, the clamped potential is the maximum of the logarithmic potential
and `0`. -/
theorem chartLogClamp_eq_max {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {x : X} (hx : x ∈ c.source) :
    chartLogClamp c a ρ x = max (Real.log (ρ / ‖c x - a‖)) 0 := by
  by_cases h : ‖c x - a‖ < ρ
  · have hmem : x ∈ chartBall c a ρ :=
      ⟨hx, Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact h)⟩
    rw [chartLogClamp_of_mem hmem, max_eq_left]
    rcases (norm_nonneg (c x - a)).eq_or_lt with h0 | h0
    · rw [← h0, div_zero, Real.log_zero]
    · exact Real.log_nonneg ((one_le_div h0).mpr h.le)
  · rw [chartLogClamp_of_not_mem (fun hmem => h (by
      have h2 := Metric.mem_ball.mp hmem.2
      rw [dist_eq_norm] at h2
      exact h2)), max_eq_right]
    rcases (norm_nonneg (c x - a)).eq_or_lt with h0 | h0
    · rw [← h0, div_zero, Real.log_zero]
    · exact Real.log_nonpos (div_pos hρ h0).le ((div_le_one h0).mpr (not_lt.mp h))

/-- The clamped logarithmic potential is non-negative. -/
theorem chartLogClamp_nonneg {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (x : X) : 0 ≤ chartLogClamp c a ρ x := by
  by_cases hx : x ∈ chartBall c a ρ
  · rw [chartLogClamp_of_mem hx]
    rcases (norm_nonneg (c x - a)).eq_or_lt with h0 | h0
    · rw [← h0, div_zero, Real.log_zero]
    · refine Real.log_nonneg ((one_le_div h0).mpr ?_)
      have h2 := Metric.mem_ball.mp hx.2
      rw [dist_eq_norm] at h2
      exact h2.le
  · rw [chartLogClamp_of_not_mem hx]

/-- On a smaller chart ball, the clamped potential dominates `log (ρ / s)`. -/
theorem chartLogClamp_lower_bound {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s ≤ ρ) {x : X} (hx : x ∈ chartBall c a s)
    (hxne : c x ≠ a) : Real.log (ρ / s) ≤ chartLogClamp c a ρ x := by
  have hmem : x ∈ chartBall c a ρ :=
    ⟨hx.1, Metric.ball_subset_ball hsρ hx.2⟩
  rw [chartLogClamp_of_mem hmem]
  have hnormpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
  have h2 := Metric.mem_ball.mp hx.2
  rw [dist_eq_norm] at h2
  refine Real.log_le_log (div_pos hρ hs) ?_
  exact div_le_div_of_nonneg_left (a := ρ) (b := s) (c := ‖c x - a‖) hρ.le hnormpos h2.le

/-- The clamped potential is strictly positive on any smaller chart ball, when `s < ρ`. -/
theorem chartLogClamp_pos {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s : ℝ}
    (hs : 0 < s) (hsρ : s < ρ) {x : X} (hx : x ∈ chartBall c a s) (hxne : c x ≠ a) :
    0 < chartLogClamp c a ρ x := by
  have hρ : 0 < ρ := lt_trans hs hsρ
  have hlog : 0 < Real.log (ρ / s) := Real.log_pos ((one_lt_div hs).mpr hsρ)
  exact lt_of_lt_of_le hlog (chartLogClamp_lower_bound hρ hs hsρ.le hx hxne)

/-- A smaller chart ball around a point of the source, with `c b = a`, is a neighbourhood of
`b` (for positive radius). -/
theorem chartBall_mem_nhds {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {s : ℝ} (hs : 0 < s)
    {b : X} (hb : b ∈ c.source) (hab : c b = a) :
    chartBall c a s ∈ 𝓝 b := by
  have h1 : c ⁻¹' Metric.ball a s ∈ 𝓝 b :=
    (c.continuousAt hb).preimage_mem_nhds (by
      rw [← hab]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs))
  have h2 : c.source ∈ 𝓝 b := c.open_source.mem_nhds hb
  have h3 : c.source ∩ c ⁻¹' Metric.ball a s ∈ 𝓝 b := inter_mem h2 h1
  simpa only [chartBall] using h3

end ChartLogClamp

/-! ## The closure of a chart ball -/

section Closure

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The closure of a chart ball is contained in the (compact) inverse image of the closed ball,
provided the closed ball lies in the target of the chart. -/
theorem closure_chartBall_subset {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) :
    closure (chartBall c a ρ) ⊆ c.symm '' Metric.closedBall a ρ := by
  have himg : chartBall c a ρ ⊆ c.symm '' Metric.closedBall a ρ := by
    rintro x ⟨hxsrc, hxball⟩
    exact ⟨c x, Metric.ball_subset_closedBall hxball, c.left_inv hxsrc⟩
  have hclosed : IsClosed (c.symm '' Metric.closedBall a ρ) :=
    (isCompact_closedBall a ρ).image_of_continuousOn (c.continuousOn_symm.mono hsub) |>.isClosed
  calc closure (chartBall c a ρ) ⊆ closure (c.symm '' Metric.closedBall a ρ) :=
        closure_mono himg
    _ = c.symm '' Metric.closedBall a ρ := hclosed.closure_eq

/-- Outside the source of the chart, the clamped potential vanishes on a neighbourhood. -/
theorem chartLogClamp_eventually_eq_zero {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) {x : X} (hx : x ∉ c.source) :
    chartLogClamp c a ρ =ᶠ[𝓝 x] 0 := by
  have hsub_cl : closure (chartBall c a ρ) ⊆ c.symm '' Metric.closedBall a ρ :=
    closure_chartBall_subset hsub
  have hclosed : IsClosed (c.symm '' Metric.closedBall a ρ) :=
    (isCompact_closedBall a ρ).image_of_continuousOn (c.continuousOn_symm.mono hsub) |>.isClosed
  have hxnot : x ∉ c.symm '' Metric.closedBall a ρ := by
    rintro ⟨w, hw, hwx⟩
    exact hx (hwx ▸ c.map_target (hsub hw))
  have hopen : (c.symm '' Metric.closedBall a ρ)ᶜ ∈ 𝓝 x :=
    hclosed.isOpen_compl.mem_nhds hxnot
  filter_upwards [hopen] with y hy
  refine chartLogClamp_of_not_mem (fun hyA => hy ?_)
  exact hsub_cl (subset_closure hyA)

end Closure

/-! ## Continuity of the clamped logarithmic potential -/

section Continuity

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The logarithmic potential `w ↦ log (ρ / ‖w - a‖)` is harmonic away from `a`. -/
theorem harmonicAt_log_div (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ≠ a) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log (ρ / ‖w - a‖)) z := by
  have hbase : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w - a‖) z :=
    harmonicAt_log_norm_sub hz
  have hsum : InnerProductSpace.HarmonicAt
      (fun w : ℂ => Real.log ρ + -(Real.log ‖w - a‖)) z :=
    (InnerProductSpace.harmonicAt_const (Real.log ρ)).add hbase.neg
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hsum
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  have hnorm : ‖w - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)
  rw [Real.log_div hρ.ne' hnorm]
  ring

/-- **Continuity of the clamped logarithmic potential away from the pole.** -/
theorem continuousAt_chartLogClamp {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) {b x : X} (hb : b ∈ c.source)
    (hab : c b = a) (hx : x ≠ b) : ContinuousAt (chartLogClamp c a ρ) x := by
  by_cases hxsrc : x ∈ c.source
  · -- inside the source: the clamped potential agrees with `max (log potential) 0`
    have hxne : c x ≠ a := by
      intro h
      exact hx (c.injOn hxsrc hb (by rw [h, hab]))
    have hcont : ContinuousAt (fun y : X => max (Real.log (ρ / ‖c y - a‖)) 0) x := by
      have h1 : ContinuousAt (fun y : X => c y - a) x :=
        (c.continuousAt hxsrc).sub continuousAt_const
      have h2 : ContinuousAt (fun y : X => ‖c y - a‖) x := h1.norm
      have hne' : (fun y : X => ‖c y - a‖) x ≠ 0 := by
        simpa using norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxne)
      have h3 : ContinuousAt (fun y : X => ρ / ‖c y - a‖) x :=
        continuousAt_const.div h2 hne'
      have h4 : ContinuousAt (fun y : X => Real.log (ρ / ‖c y - a‖)) x :=
        h3.log (div_ne_zero hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxne)))
      have h5 : ContinuousAt (fun y : X => max (Real.log (ρ / ‖c y - a‖)) 0) x := by
        have h6 := h4.sup (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x)
        simpa only [Pi.sup_apply, Pi.zero_apply] using h6
      exact h5
    refine hcont.congr ?_
    filter_upwards [c.open_source.mem_nhds hxsrc] with y hy
    exact (chartLogClamp_eq_max hρ hy).symm
  · -- outside the source: the clamped potential vanishes on a neighbourhood
    have hev := (chartLogClamp_eventually_eq_zero hsub hxsrc).symm
    exact continuousAt_const.congr hev

end Continuity

/-! ## Subharmonicity of the clamped logarithmic potential -/

section Subharmonic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A point of the ball `Metric.ball b ρ'` stays away from `a` when `ρ' ≤ ‖b - a‖`. -/
theorem norm_sub_pos_of_mem_ball {a b z : ℂ} {ρ' : ℝ} (hρ' : ρ' ≤ ‖b - a‖)
    (hz : z ∈ Metric.ball b ρ') : 0 < ‖z - a‖ := by
  have h1 : ‖b - a‖ ≤ ‖b - z‖ + ‖z - a‖ := by
    calc ‖b - a‖ = ‖(b - z) + (z - a)‖ := by congr 1; ring
      _ ≤ ‖b - z‖ + ‖z - a‖ := norm_add_le _ _
  have h2 := Metric.mem_ball.mp hz
  rw [dist_eq_norm] at h2
  rw [norm_sub_rev b z] at h1
  linarith

/-- **The clamped logarithmic potential satisfies the circle mean-value inequality** in the
coordinates of the chart, away from the pole. -/
theorem SubharmonicAtChart_chartLogClamp {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) {x : X} (hx : x ∈ c.source)
    (hxne : c x ≠ a) : SubharmonicAtChart (chartLogClamp c a ρ) c x := by
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hx))
  have hxpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
  set ρ' : ℝ := min ε ‖c x - a‖ with hρ'def
  have hρ' : 0 < ρ' := lt_min hε hxpos
  have hρ'ε : ρ' ≤ ε := min_le_left _ _
  have hρ'norm : ρ' ≤ ‖c x - a‖ := min_le_right _ _
  have htgt : Metric.ball (c x) ρ' ⊆ c.target := (Metric.ball_subset_ball hρ'ε).trans hεsub
  -- the Euclidean logarithmic potential
  set u : ℂ → ℝ := fun w => Real.log (ρ / ‖w - a‖) with hudef
  have hu : ∀ z : ℂ, ‖z - c x‖ < ρ' → InnerProductSpace.HarmonicAt u z := by
    intro z hz
    have hza : z ≠ a :=
      sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt (norm_sub_pos_of_mem_ball hρ'norm
        (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hz)))))
    exact harmonicAt_log_div a hρ hza
  have hmvp : ∀ z : ℂ, ‖z - c x‖ < ρ' → ∀ r : ℝ, 0 < r →
      Metric.closedBall z r ⊆ Metric.ball (c x) ρ' →
      max (u z) 0 ≤ Real.circleAverage (fun w : ℂ => max (u w) 0) z r :=
    Commons.Analysis.Complex.Harmonic.subMeanValue_max_const hρ' hu
  refine ⟨hx, ρ', hρ', htgt, ?_, ?_⟩
  · -- continuity of the pulled back clamped potential on the chart ball
    have hcontu : ContinuousOn (fun y : ℂ => max (u y) 0) (Metric.ball (c x) ρ') := by
      refine continuousOn_of_forall_continuousAt (fun z hz => ?_)
      have hza : z ≠ a :=
        sub_ne_zero.mp (norm_ne_zero_iff.mp (ne_of_gt (norm_sub_pos_of_mem_ball hρ'norm hz)))
      have h6 := (harmonicAt_log_div a hρ hza).1.continuousAt.sup
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z)
      simpa only [Pi.sup_apply, Pi.zero_apply] using h6
    refine hcontu.congr (fun y hy => ?_)
    have hysrc : c.symm y ∈ c.source := c.map_target (htgt hy)
    have hyl : c (c.symm y) = y := c.right_inv (htgt hy)
    show chartLogClamp c a ρ (c.symm y) = max (u y) 0
    rw [chartLogClamp_eq_max hρ hysrc, hyl, hudef]
  · intro p hp r hr hpr
    have hp' : ‖p - c x‖ < ρ' := by
      have h := Metric.mem_ball.mp hp
      rwa [dist_eq_norm] at h
    have hpmvp := hmvp p hp' r hr hpr
    have hsphere : ∀ w ∈ Metric.sphere p r, chartLogClamp c a ρ (c.symm w) = max (u w) 0 := by
      intro w hw
      have hwtgt : w ∈ c.target := htgt (hpr (Metric.sphere_subset_closedBall hw))
      have hwsrc : c.symm w ∈ c.source := c.map_target hwtgt
      have hwl : c (c.symm w) = w := c.right_inv hwtgt
      rw [chartLogClamp_eq_max hρ hwsrc, hwl, hudef]
    have hptgt : p ∈ c.target := htgt hp
    have hpsrc : c.symm p ∈ c.source := c.map_target hptgt
    have hpl : c (c.symm p) = p := c.right_inv hptgt
    have hpval : chartLogClamp c a ρ (c.symm p) = max (u p) 0 := by
      rw [chartLogClamp_eq_max hρ hpsrc, hpl, hudef]
    have havg : Real.circleAverage (chartLogClamp c a ρ ∘ c.symm) p r
        = Real.circleAverage (fun w : ℂ => max (u w) 0) p r :=
      Real.circleAverage_congr_sphere (fun w hw =>
        hsphere w (by simpa [abs_of_pos hr] using hw))
    rw [Function.comp_apply, hpval, havg]
    exact hpmvp

/-- **The clamped logarithmic potential is subharmonic on `X` minus the pole.** -/
theorem subharmonicOnX_chartLogClamp {z₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ z₀) z₀) ρ ⊆ (chartAt ℂ z₀).target) :
    SubharmonicOnX (chartLogClamp (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ) (univ \ {z₀}) := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀ with hc
  set a : ℂ := c z₀ with ha
  have hz₀src : z₀ ∈ c.source := mem_chart_source ℂ z₀
  have hsub' : Metric.closedBall a ρ ⊆ c.target := hsub
  constructor
  · -- continuity on `univ ∖ {z₀}`
    refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
    exact continuousAt_chartLogClamp hρ hsub' hz₀src rfl hx.2
  · intro x hx
    by_cases hxsrc : x ∈ c.source
    · -- inside the source: use the chart-mean-value inequality in the chart at `x`
      have hxne : c x ≠ a := by
        intro h
        exact hx.2 (c.injOn hxsrc hz₀src (by rw [h, ha]))
      have hchart : SubharmonicAtChart (chartLogClamp c a ρ) c x :=
        SubharmonicAtChart_chartLogClamp hρ hxsrc hxne
      exact (SubharmonicAtChart_iff_chartAt (u := chartLogClamp c a ρ) (a := x) (b := z₀)
        (by simpa [hc] using hxsrc)).mpr hchart
    · -- outside the source: the clamped potential vanishes on a neighbourhood
      have hev : chartLogClamp c a ρ =ᶠ[𝓝 x] 0 := chartLogClamp_eventually_eq_zero hsub' hxsrc
      exact SubharmonicOnXAt.congr (harmonicOnXAt_const (0 : ℝ)).subharmonic hev.symm

end Subharmonic

end Submission
