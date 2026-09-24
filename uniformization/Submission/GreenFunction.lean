import ChallengeDeps
import Submission.Balayage
import Submission.DirichletX
import Submission.MaxPrincipleRegion
import Submission.Commons.Analysis.Complex.Harmonic.annulus_le_boundary
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd

/-!
# Toward the Green function: the log-ratio (two-constants) estimate for the hitting probability

The Green function of `X` with pole `z₀` is obtained from the normalised hitting probabilities
`(-log ρ) · hittingProbability c a ρ` in the limit `ρ → 0`.  The decisive estimate which controls
this limit is the classical *two-constants* (harmonic measure) bound: the hitting probability of a
chart disc of radius `ρ` dominates the harmonic measure of that disc in a larger chart ball of
radius `ρ₂`, i.e.

`Real.log (ρ₂ / ‖c x - a‖) / Real.log (ρ₂ / ρ) ≤ hittingProbability c a ρ x`

for `ρ ≤ ‖c x - a‖ ≤ ρ₂`.  In the limit `ρ → 0` this gives the lower bound `log (ρ₂ / ‖c x - a‖)`
for the Green function.

This module collects the ingredients: the maximum principle for harmonic functions on a closed
annulus (commons `annulus_le_boundary`, translated to an arbitrary centre), and the harmonicity on
`X` of the logarithm of the modulus of a chart coordinate (which uses the analyticity of the chart
transitions, commons `chart_transition_analyticOnNhd`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

/-! ## The maximum principle on a closed annulus with an arbitrary centre -/

/-- **Maximum principle on a closed annulus** (arbitrary centre): a function harmonic on the open
annulus `r < ‖z - a‖ < R`, continuous on the closed annulus, and bounded by `M` on the two
boundary circles, is bounded by `M` on the whole closed annulus.  This is the commons lemma
`annulus_le_boundary` translated by `a`. -/
theorem annulus_le_boundary_center {u : ℂ → ℝ} {a : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | r < ‖z - a‖ ∧ ‖z - a‖ < R})
    (hc : ContinuousOn u {z : ℂ | r ≤ ‖z - a‖ ∧ ‖z - a‖ ≤ R})
    (hM : ∀ z : ℂ, (‖z - a‖ = r ∨ ‖z - a‖ = R) → u z ≤ M) :
    ∀ z : ℂ, r ≤ ‖z - a‖ → ‖z - a‖ ≤ R → u z ≤ M := by
  set v : ℂ → ℝ := fun w => u (a + w) with hv
  have hvhar : InnerProductSpace.HarmonicOnNhd v {w : ℂ | r < ‖w‖ ∧ ‖w‖ < R} := by
    intro w hw
    have h1 : InnerProductSpace.HarmonicAt u (a + w) := hu (a + w) (by simpa using hw)
    have h2 : AnalyticAt ℂ (fun z : ℂ => a + z) w := analyticAt_const.add analyticAt_id
    have h3 : InnerProductSpace.HarmonicAt (fun z : ℂ => u (a + z)) w :=
      Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic h2 h1
    simpa [hv] using h3
  have hvcont : ContinuousOn v {w : ℂ | r ≤ ‖w‖ ∧ ‖w‖ ≤ R} := by
    have hmap : ContinuousOn (fun w : ℂ => a + w) {w : ℂ | r ≤ ‖w‖ ∧ ‖w‖ ≤ R} :=
      (continuous_const.add continuous_id).continuousOn
    have hmaps : MapsTo (fun w : ℂ => a + w) {w : ℂ | r ≤ ‖w‖ ∧ ‖w‖ ≤ R}
        {z : ℂ | r ≤ ‖z - a‖ ∧ ‖z - a‖ ≤ R} := by
      intro w hw
      simpa using hw
    have h := hc.comp hmap hmaps
    simpa [hv, Function.comp_def] using h
  have hMv : ∀ w : ℂ, (‖w‖ = r ∨ ‖w‖ = R) → v w ≤ M := by
    intro w hw
    refine hM (a + w) ?_
    rcases hw with h | h
    · left; simpa using h
    · right; simpa using h
  intro z hzr hzR
  have h := Commons.Analysis.Complex.Harmonic.annulus_le_boundary hr hrR hvhar hvcont hMv
    (z - a) (by simpa using hzr) (by simpa using hzR)
  rw [hv] at h
  simpa using h

/-! ## Harmonicity of the logarithm of the modulus of a chart coordinate -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The local model: `z ↦ Real.log ‖z - a‖` is harmonic at every `z ≠ a`. -/
theorem harmonicAt_log_norm_sub {a z : ℂ} (hz : z ≠ a) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w - a‖) z :=
  AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - a)
    (analyticAt_id.sub analyticAt_const) (by simpa using sub_ne_zero.mpr hz)

/-- `x ↦ Real.log ‖c x - c z₀‖` is harmonic on `X` at every point `x` of the source of the
preferred chart at `z₀` at which it is nonzero. -/
theorem harmonicOnXAt_log_norm_chartAt {z₀ x : X} (hx : x ∈ (chartAt ℂ z₀).source)
    (hne : chartAt ℂ z₀ x ≠ chartAt ℂ z₀ z₀) :
    HarmonicOnXAt (fun y => Real.log ‖chartAt ℂ z₀ y - chartAt ℂ z₀ z₀‖) x := by
  rw [HarmonicOnXAt_iff_chart hx]
  set ξ₀ : ℂ := (chartAt ℂ z₀) x with hξ₀
  set a : ℂ := (chartAt ℂ z₀) z₀ with ha
  have hmodel : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w - a‖) ξ₀ :=
    harmonicAt_log_norm_sub (by rw [hξ₀, ha]; exact hne)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hmodel
  have hξ₀tgt : ξ₀ ∈ (chartAt ℂ z₀).target := hξ₀ ▸ (chartAt ℂ z₀).map_source hx
  have htgt : (chartAt ℂ z₀).target ∈ 𝓝 ξ₀ :=
    (chartAt ℂ z₀).open_target.mem_nhds hξ₀tgt
  filter_upwards [htgt] with ξ hξ
  simp only [Function.comp_apply]
  rw [(chartAt ℂ z₀).right_inv hξ]


/-! ## The hitting probability on the closed chart disc

The members of the balayage family are *continuous*, so the constraint `v ≤ -1` imposed on the
open chart disc propagates to its closure: every member satisfies `v ≤ -1` on the whole closed
chart disc.  Taking the envelope gives `hittingProbability c a ρ = 1` on the closed chart disc,
which is the starting point of every comparison argument for the hitting probability. -/

section ClosedBall

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The closed chart disc of radius `ρ > 0` is contained in the closure of the open chart disc. -/
theorem chartClosedBall_subset_closure_chartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    chartClosedBall c a ρ ⊆ closure (chartBall c a ρ) := by
  intro x hx
  have hxs : x ∈ c.source := hx.1
  have hζclos : c x ∈ closure (Metric.ball a ρ) := by
    rw [closure_ball _ hρ.ne']
    exact hx.2
  rw [mem_closure_iff_nhds]
  intro o ho
  have h2 : c '' (o ∩ c.source) ∈ 𝓝 (c x) :=
    c.image_mem_nhds hxs (Filter.inter_mem ho (c.open_source.mem_nhds hxs))
  obtain ⟨ζ, ⟨w, hw, rfl⟩, hζball⟩ := (mem_closure_iff_nhds.mp hζclos) _ h2
  exact ⟨w, hw.1, hw.2, hζball⟩

/-- Every member of the balayage family is `≤ -1` on the whole closed chart disc. -/
theorem hittingFamily_le_neg_one_of_mem_chartClosedBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) {v : X → ℝ}
    (hv : v ∈ hittingFamily c a ρ) {x : X} (hx : x ∈ chartClosedBall c a ρ) : v x ≤ -1 := by
  have hclo : x ∈ closure (chartBall c a ρ) := chartClosedBall_subset_closure_chartBall hρ hsub hx
  have hne : (𝓝[chartBall c a ρ] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclo
  haveI := hne
  have hcont : ContinuousAt v x := (hv.1.1).continuousAt Filter.univ_mem
  have hT : Tendsto v (𝓝[chartBall c a ρ] x) (𝓝 (v x)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ z in 𝓝[chartBall c a ρ] x, v z ≤ -1 :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hv.2.1 z hz)
  exact le_of_tendsto hT hev

/-- **The hitting probability equals `1` on the closed chart disc.** -/
theorem hittingProbability_eq_one_of_mem_chartClosedBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) {x : X}
    (hx : x ∈ chartClosedBall c a ρ) : hittingProbability c a ρ x = 1 := by
  refine le_antisymm (hittingProbability_le_one c a ρ x) ?_
  have hbal : balayage c a ρ x ≤ -1 := by
    rw [balayage, upperEnvelope]
    refine csSup_le ((hittingFamily_nonempty c a ρ).image _) ?_
    rintro y ⟨v, hv, rfl⟩
    exact hittingFamily_le_neg_one_of_mem_chartClosedBall hρ hsub hv hx
  rw [hittingProbability]
  linarith

end ClosedBall


/-! ## The two-constants (harmonic measure) estimate for the hitting probability

The classical estimate which controls the limit `ρ → 0` of the normalised hitting probabilities
`(-log ρ) · h_ρ`: the hitting probability of the chart disc of radius `ρ` dominates the harmonic
measure of that disc in a strictly larger chart ball of radius `ρ₂`,

`log (ρ₂ / ‖c x - a‖) / log (ρ₂ / ρ) ≤ hittingProbability c a ρ x`  for `ρ < ‖c x - a‖ < ρ₂`.

The proof is the classical one: for every member `v` of the balayage family, the function
`v + (the log-ratio)` is subharmonic on the chart annulus and has boundary values `≤ 0` on the
inner sphere (where `v ≤ -1` and the log-ratio is `1`) and on the outer sphere (where `v ≤ 0` and
the log-ratio is `0`); the maximum principle gives `v ≤ -(log-ratio)`, whence the envelope. -/

section TwoConstants

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The closure of the open chart disc of positive radius is the closed chart disc. -/
theorem closure_chartBall_eq_chartClosedBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    closure (chartBall c a ρ) = chartClosedBall c a ρ :=
  Subset.antisymm (closure_chartBall_subset_chartClosedBall hsub)
    (chartClosedBall_subset_closure_chartBall hρ hsub)

/-- The frontier of the open annulus `chartBall ρ₂ \ chartClosedBall ρ` lies in the two spheres. -/
theorem frontier_chartBall_diff_chartClosedBall_subset {c : OpenPartialHomeomorph X ℂ} {a : ℂ}
    {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (hsub : Metric.closedBall a ρ₂ ⊆ c.target) :
    frontier (chartBall c a ρ₂ \ chartClosedBall c a ρ) ⊆
      chartSphere c a ρ₂ ∪ chartSphere c a ρ := by
  have hρ₂ : 0 < ρ₂ := lt_trans hρ hρρ₂
  have hsubρ : Metric.closedBall a ρ ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hρρ₂.le).trans hsub
  set U : Set X := chartBall c a ρ₂ \ chartClosedBall c a ρ with hU
  have hfront : frontier U ⊆ closure (chartBall c a ρ₂) ∩ ((chartBall c a ρ₂)ᶜ ∪ chartClosedBall c a ρ) := by
    have h1 : frontier U ⊆ closure (chartBall c a ρ₂) :=
      frontier_subset_closure.trans (closure_mono Set.diff_subset)
    have h2 : frontier U ⊆ closure (Uᶜ) := by
      rw [frontier_eq_closure_inter_closure]
      exact Set.inter_subset_right
    have hsubc₂ : (Uᶜ : Set X) = (chartBall c a ρ₂)ᶜ ∪ chartClosedBall c a ρ := by
      ext z
      simp only [hU, Set.mem_compl_iff, Set.mem_sdiff, not_and, not_not, Set.mem_union]
      tauto
    have hcleq : closure (Uᶜ) = (chartBall c a ρ₂)ᶜ ∪ chartClosedBall c a ρ := by
      have hA : IsClosed ((chartBall c a ρ₂)ᶜ) := (chartBall_isOpen c a ρ₂).isClosed_compl
      have hB : IsClosed (chartClosedBall c a ρ) := isClosed_chartClosedBall hsubρ
      rw [hsubc₂, closure_union, hA.closure_eq, hB.closure_eq]
    rw [hcleq] at h2
    exact fun z hz => ⟨h1 hz, h2 hz⟩
  intro ξ hξ
  obtain ⟨hξc, hξrest⟩ := hfront hξ
  have hξcl2 : ξ ∈ chartClosedBall c a ρ₂ := by
    rw [← closure_chartBall_eq_chartClosedBall hρ₂ hsub]
    exact hξc
  have hξcl : ξ ∈ closure U := frontier_subset_closure hξ
  have hunion : ξ ∈ (chartBall c a ρ₂)ᶜ ∪ chartClosedBall c a ρ := hξrest
  rcases hunion with hout | hin
  · -- ξ is outside the open outer ball, but in the closed outer ball: on the outer sphere
    left
    have hd1 : dist (c ξ) a ≤ ρ₂ := by
      simpa [Metric.mem_closedBall] using hξcl2.2
    have hd2 : ¬ (dist (c ξ) a < ρ₂) := by
      intro hlt
      exact hout (by rw [mem_chartBall]; exact ⟨chartClosedBall_subset_source c a ρ₂ hξcl2,
        by rwa [Metric.mem_ball]⟩)
    rw [mem_chartSphere, Metric.mem_sphere]
    exact ⟨chartClosedBall_subset_source c a ρ₂ hξcl2, le_antisymm hd1 (le_of_not_gt hd2)⟩
  · -- ξ is in the closed inner ball; it cannot be in the open inner ball
    have hnot : ξ ∉ chartBall c a ρ := by
      intro hb
      have hsubc : chartBall c a ρ ⊆ (chartBall c a ρ₂ \ chartClosedBall c a ρ)ᶜ := by
        intro z hz hzU
        exact hzU.2 (chartBall_subset_chartClosedBall c a ρ hz)
      have hint : ξ ∈ interior (Uᶜ) := interior_maximal hsubc (chartBall_isOpen c a ρ) hb
      have hint' : ξ ∈ (closure U)ᶜ := by
        rw [← interior_compl]
        exact hint
      exact hint' (frontier_subset_closure hξ)
    right
    have hd1 : dist (c ξ) a ≤ ρ := by
      simpa [Metric.mem_closedBall] using hin.2
    have hd2 : ¬ (dist (c ξ) a < ρ) := by
      intro hlt
      exact hnot (by rw [mem_chartBall]; exact ⟨chartClosedBall_subset_source c a ρ hin,
        by rwa [Metric.mem_ball]⟩)
    rw [mem_chartSphere, Metric.mem_sphere]
    exact ⟨chartClosedBall_subset_source c a ρ hin, le_antisymm hd1 (le_of_not_gt hd2)⟩

end TwoConstants


end Submission
