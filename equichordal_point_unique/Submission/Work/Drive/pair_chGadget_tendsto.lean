import Mathlib
import Submission.Work.Drive.chartGadget
import Submission.Work.Drive.continuousAt_chGadget
import Submission.Work.Drive.pair_gadget_tendsto
import Submission.Work.Drive.tendsto_chart_transition_slope
import Submission.Work.Drive.deriv_chart_transition_ne_zero
import Submission.Work.Analysis.RiemannSurface.chart_transition_analytic

/-!
# The limit of the product of two consecutive transfer gadgets at the shared pivot,
for an *arbitrary chart family* `c` out of the maximal atlas

This is the chart-family version of `Work.Drive.pair_gadget_tendsto`: the two gadgets are
`chGadget c a ρ (j-1)` and `chGadget c a ρ j`, both built with the chosen charts `c (j-1)`, `c j`
(see `Submission/Work/Drive/chartGadget.lean`), rather than with the preferred charts
`chartAt ℂ (a (j-1))`, `chartAt ℂ (a j)`.

The mathematics is word for word the same as in `Work.Drive.pair_gadget_tendsto`.  In a
neighbourhood of `a j` both gadgets are given by the phase of the ratio of the two chart
differences (`Work.Drive.chGadget_eq_phase`), and the two singular factors
`phase ((c (j-1)) x - (c (j-1)) (a j))` and `phase ((c j) x - (c j) (a j))` cancel against each
other because the chart transition `(c (j-1)).symm.trans (c j)` is a local biholomorphism with
**non-zero** derivative at `(c (j-1)) (a j)`
(`Work.Drive.phase_ratio_mul`, `Work.Drive.deriv_transition_ne_zero_of_mem_maximalAtlas`).  The
latter is *not* a hypothesis here: it is derived from `c (j-1)`, `c j` lying in the maximal atlas.

The three surviving factors are `A x = (c (j-1)) x - (c (j-1)) (a (j-1))`, the chart-transition
slope `C x / B x = ((c j) x - (c j) (a j)) / ((c (j-1)) x - (c (j-1)) (a j))` (whose limit is the
derivative of the transition, `Work.Drive.tendsto_transition_slope_of_mem_maximalAtlas`) and
`D x = (c j) x - (c j) (a (j+1))`.  Each of the three phases has a non-zero limit, so the product
does too.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

/-! ## Chart transitions between charts of the maximal atlas -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart transitions between two members of the maximal atlas are complex analytic.**  This is
`Submission/Work/Analysis/RiemannSurface/chart_transition_analytic.lean` with the atlas membership
replaced by the membership in the maximal atlas. -/
theorem analyticAt_transition_of_mem_maximalAtlas {c₀ c₁ : OpenPartialHomeomorph X ℂ}
    (hc₀ : c₀ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hc₁ : c₁ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    {w : ℂ} (hw : w ∈ (c₀.symm.trans c₁).source) :
    AnalyticAt ℂ ((c₀.symm.trans c₁) : ℂ → ℂ) w := by
  have hmem : (c₀.symm.trans c₁) ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas hc₀ hc₁
  have hcd : ContDiffOn ℂ 1 ((c₀.symm.trans c₁ : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      (c₀.symm.trans c₁).source := by
    have h := (mem_groupoid_of_pregroupoid.mp hmem).1
    simpa [contDiffPregroupoid] using h
  exact (hcd.differentiableOn one_ne_zero).analyticAt
    ((c₀.symm.trans c₁).open_source.mem_nhds hw)

/-- **The transition between two members of the maximal atlas has non-zero derivative where it is
defined.**  Here `y` lies in both charts, so that `c₀ y` is a point of the source of the
transition.  The transition is the germ of a local biholomorphism, hence injective near `c₀ y`, so
its derivative cannot vanish
(`Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`). -/
theorem deriv_transition_ne_zero_of_mem_maximalAtlas {c₀ c₁ : OpenPartialHomeomorph X ℂ}
    (hc₀ : c₀ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hc₁ : c₁ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    {y : X} (hy₀ : y ∈ c₀.source) (hy₁ : y ∈ c₁.source) :
    deriv ((c₀.symm.trans c₁) : ℂ → ℂ) (c₀ y) ≠ 0 := by
  have hmem : c₀ y ∈ (c₀.symm.trans c₁).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨c₀.map_source hy₀, ?_⟩
    show c₀.symm (c₀ y) ∈ c₁.source
    rw [c₀.left_inv hy₀]
    exact hy₁
  obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp (c₀.symm.trans c₁).open_source _ hmem
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hrpos
    (analyticAt_transition_of_mem_maximalAtlas hc₀ hc₁ hmem)
    ((c₀.symm.trans c₁).injOn.mono hrsub)

/-- **The difference quotient of a chart transition, for charts of the maximal atlas.**  As
`z → y` along the punctured neighbourhood, the slope
`((c₁ z - c₁ y)) / ((c₀ z - c₀ y))` converges to the derivative of the transition
`c₀.symm.trans c₁` at `c₀ y`.  This is
`Work.Drive.tendsto_chart_transition_slope` for charts of the maximal atlas. -/
theorem tendsto_transition_slope_of_mem_maximalAtlas {c₀ c₁ : OpenPartialHomeomorph X ℂ}
    (hc₀ : c₀ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hc₁ : c₁ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    {y : X} (hy₀ : y ∈ c₀.source) (hy₁ : y ∈ c₁.source) :
    Filter.Tendsto (fun z : X => (c₁ z - c₁ y) / (c₀ z - c₀ y))
      (nhdsWithin y {y}ᶜ)
      (nhds (deriv ((c₀.symm.trans c₁) : ℂ → ℂ) (c₀ y))) := by
  have hmem : c₀ y ∈ (c₀.symm.trans c₁).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨c₀.map_source hy₀, ?_⟩
    show c₀.symm (c₀ y) ∈ c₁.source
    rw [c₀.left_inv hy₀]
    exact hy₁
  have hc0c : ContinuousAt (↑c₀ : X → ℂ) y := c₀.continuousAt hy₀
  have hana : AnalyticAt ℂ (((c₀.symm.trans c₁) : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      (c₀ y) := analyticAt_transition_of_mem_maximalAtlas hc₀ hc₁ hmem
  have hderiv : HasDerivAt (((c₀.symm.trans c₁) : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      (deriv (((c₀.symm.trans c₁) : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ) (c₀ y)) (c₀ y) :=
    hana.differentiableAt.hasDerivAt
  -- the chart `c₀` carries the punctured neighbourhood of `y` into that of `c₀ y`
  have hφ : Filter.Tendsto (fun z : X => c₀ z) (𝓝[≠] y) (𝓝[≠] (c₀ y)) := by
    rw [nhdsWithin, nhdsWithin, Filter.tendsto_inf]
    refine ⟨hc0c.tendsto.mono_left inf_le_left, ?_⟩
    rw [Filter.tendsto_principal]
    refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (c₀.open_source.mem_nhds hy₀))) ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz1 ⊢
    exact fun hcon => hz1 (c₀.injOn hz2 hy₀ hcon)
  -- finish: the difference quotient is the slope of the transition, composed with `c₀`
  refine Filter.Tendsto.congr' ?_ (hderiv.tendsto_slope.comp hφ)
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨c₀.source ∩ c₁.source, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds ((c₀.open_source.inter c₁.open_source).mem_nhds ⟨hy₀, hy₁⟩)
  · intro z hz
    obtain ⟨hz0, hz1⟩ := hz
    simp only [Function.comp_apply]
    rw [slope_def_field, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
      c₀.left_inv hz0, c₀.left_inv hy₀]

end Work.Drive

/-! ## The limit of the product of two consecutive gadgets -/

namespace Work.Drive

open LeanEval.Geometry

theorem pair_chGadget_tendsto {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hca : ∀ i : ℕ, c i ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hρ : ∀ i : ℕ, 0 < ρ i)
    (hstep : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source ∧
      ‖(c i) (a (i + 1)) - (c i) (a i)‖ < ρ i)
    (hinj : Function.Injective a) :
    ∃ w : ℂ, w ≠ 0 ∧ Filter.Tendsto (fun x : X =>
        Work.Drive.chGadget c a ρ (j - 1) x * Work.Drive.chGadget c a ρ j x)
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds w) := by
  classical
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  -- membership of the three pivots in the relevant chart sources
  have hsrc_prev' : a (j - 1) ∈ (c (j - 1)).source := (hstep (j - 1)).1
  have hsrc_prev : a j ∈ (c (j - 1)).source := by
    simpa only [hj'] using (hstep (j - 1)).2.1
  have hstep_j := hstep j
  have hsrc_j : a j ∈ (c j).source := hstep_j.1
  have hsrc_j_next : a (j + 1) ∈ (c j).source := hstep_j.2.1
  have hball_prev : ‖(c (j - 1)) (a j) - chP c a (j - 1)‖ < ρ (j - 1) := by
    simpa only [chP, chQ, hj'] using (hstep (j - 1)).2.2
  -- the pivots are pairwise distinct
  have hne_j_prev : a j ≠ a (j - 1) := fun h => (by omega : j ≠ j - 1) (hinj h)
  have hne_j_next : a j ≠ a (j + 1) := fun h => (by omega : j ≠ j + 1) (hinj h)
  have hP1_ne : (c (j - 1)) (a j) ≠ chP c a (j - 1) := by
    intro h
    exact hne_j_prev ((c (j - 1)).injOn hsrc_prev hsrc_prev' h)
  have hQ1 : chQ c a (j - 1) = (c (j - 1)) (a j) := by rw [chQ, hj']
  have hP2_ne_Q2 : chP c a j ≠ chQ c a j := by
    intro h
    exact (by omega : j ≠ j + 1) (hinj ((c j).injOn hsrc_j hsrc_j_next h))
  -- the derivative of the chart transition, and its non-vanishing
  have hT : deriv (((c (j - 1)).symm.trans (c j)) : ℂ → ℂ) ((c (j - 1)) (a j)) ≠ 0 :=
    deriv_transition_ne_zero_of_mem_maximalAtlas (hca (j - 1)) (hca j) hsrc_prev hsrc_j
  -- all the eventual facts on the punctured neighbourhood of `a j`
  have h1ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ≠ a (j - 1) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_ne_nhds hne_j_prev)
  have h2ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ≠ a (j + 1) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_ne_nhds hne_j_next)
  have hsrc_prev_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ∈ (c (j - 1)).source :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((c (j - 1)).open_source.mem_nhds hsrc_prev)
  have hsrc_j_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ∈ (c j).source :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds ((c j).open_source.mem_nhds hsrc_j)
  have hball_prev_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ,
      ‖(c (j - 1)) x - chP c a (j - 1)‖ < 2 * ρ (j - 1) := by
    have hlt : ‖(c (j - 1)) (a j) - chP c a (j - 1)‖ < 2 * ρ (j - 1) := by
      linarith [hball_prev, hρ (j - 1)]
    have hcont : ContinuousAt (fun x : X =>
        ‖(c (j - 1)) x - chP c a (j - 1)‖) (a j) :=
      (((c (j - 1)).continuousAt hsrc_prev).sub continuousAt_const).norm
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt))
  have hball_j_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ,
      ‖(c j) x - chP c a j‖ < 2 * ρ j := by
    have hlt : ‖(c j) (a j) - chP c a j‖ < 2 * ρ j := by
      rw [chP, sub_self, norm_zero]
      linarith [hρ j]
    have hcont : ContinuousAt (fun x : X => ‖(c j) x - chP c a j‖) (a j) :=
      (((c j).continuousAt hsrc_j).sub continuousAt_const).norm
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt))
  -- the three factors of the limit
  have hFst : Filter.Tendsto (fun x : X => phase ((c (j - 1)) x - chP c a (j - 1)))
      (nhdsWithin (a j) {(a j)}ᶜ)
      (nhds (phase ((c (j - 1)) (a j) - chP c a (j - 1)))) := by
    refine tendsto_phase_of_tendsto ?_ (sub_ne_zero.mpr hP1_ne)
    exact (((c (j - 1)).continuousAt hsrc_prev).sub continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds
  have hmid : Filter.Tendsto (fun x : X => phase (((c j) x - chP c a j) /
      ((c (j - 1)) x - chQ c a (j - 1))))
      (nhdsWithin (a j) {(a j)}ᶜ)
      (nhds (phase (deriv (((c (j - 1)).symm.trans (c j)) : ℂ → ℂ) ((c (j - 1)) (a j))))) := by
    refine tendsto_phase_of_tendsto ?_ hT
    have h1 := tendsto_transition_slope_of_mem_maximalAtlas (hca (j - 1)) (hca j)
      hsrc_prev hsrc_j
    simpa only [chP, hQ1] using h1
  have hthird : Filter.Tendsto (fun x : X => star (phase ((c j) x - chQ c a j)))
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds (star (phase (chP c a j - chQ c a j)))) := by
    have hb : Filter.Tendsto (fun x : X => (c j) x - chQ c a j)
        (nhdsWithin (a j) {(a j)}ᶜ) (nhds (chP c a j - chQ c a j)) := by
      have hc : ContinuousAt (fun x : X => (c j) x) (a j) := (c j).continuousAt hsrc_j
      have h : Filter.Tendsto (fun x : X => (c j) x - chQ c a j) (nhds (a j))
          (nhds (chP c a j - chQ c a j)) := (hc.sub continuousAt_const).tendsto
      exact h.mono_left nhdsWithin_le_nhds
    exact (tendsto_phase_of_tendsto hb (sub_ne_zero.mpr hP2_ne_Q2)).star
  have hF : Filter.Tendsto (fun x : X => phase ((c (j - 1)) x - chP c a (j - 1)) *
      phase (((c j) x - chP c a j) / ((c (j - 1)) x - chQ c a (j - 1))) *
      star (phase ((c j) x - chQ c a j)))
      (nhdsWithin (a j) {(a j)}ᶜ)
      (nhds (phase ((c (j - 1)) (a j) - chP c a (j - 1)) *
        phase (deriv (((c (j - 1)).symm.trans (c j)) : ℂ → ℂ) ((c (j - 1)) (a j))) *
        star (phase (chP c a j - chQ c a j)))) :=
    (hFst.mul hmid).mul hthird
  -- on the punctured neighbourhood the product of the two gadgets *is* that expression
  have hev : (fun x : X => chGadget c a ρ (j - 1) x * chGadget c a ρ j x)
      =ᶠ[nhdsWithin (a j) {(a j)}ᶜ]
      (fun x : X => phase ((c (j - 1)) x - chP c a (j - 1)) *
        phase (((c j) x - chP c a j) / ((c (j - 1)) x - chQ c a (j - 1))) *
        star (phase ((c j) x - chQ c a j))) := by
    filter_upwards [self_mem_nhdsWithin, h1ev, h2ev, hsrc_prev_ev, hball_prev_ev,
      hsrc_j_ev, hball_j_ev] with x hx hne1 hne2 hs1 hb1 hs2 hb2
    have hxA : x ≠ a j := by simpa using hx
    rw [chGadget_eq_phase (c := c) (a := a) (ρ := ρ) (i := j - 1) ⟨hs1, le_of_lt hb1⟩,
      chGadget_eq_phase (c := c) (a := a) (ρ := ρ) (i := j) ⟨hs2, le_of_lt hb2⟩]
    have h1 : (c (j - 1)) x - chP c a (j - 1) ≠ 0 := by
      rw [chP]
      exact sub_ne_zero.mpr (fun h => hne1 ((c (j - 1)).injOn hs1 hsrc_prev' h))
    have h2 : (c (j - 1)) x - chQ c a (j - 1) ≠ 0 := by
      rw [hQ1]
      exact sub_ne_zero.mpr (fun h => hxA ((c (j - 1)).injOn hs1 hsrc_prev h))
    have h3 : (c j) x - chP c a j ≠ 0 := by
      rw [chP]
      exact sub_ne_zero.mpr (fun h => hxA ((c j).injOn hs2 hsrc_j h))
    have h4 : (c j) x - chQ c a j ≠ 0 := by
      rw [chQ]
      exact sub_ne_zero.mpr (fun h => hne2 ((c j).injOn hs2 hsrc_j_next h))
    exact phase_ratio_mul h1 h2 h3 h4
  refine ⟨phase ((c (j - 1)) (a j) - chP c a (j - 1)) *
      phase (deriv (((c (j - 1)).symm.trans (c j)) : ℂ → ℂ) ((c (j - 1)) (a j))) *
      star (phase (chP c a j - chQ c a j)), ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (phase_ne_zero (sub_ne_zero.mpr hP1_ne))
      (phase_ne_zero hT)) (star_ne_zero.mpr (phase_ne_zero (sub_ne_zero.mpr hP2_ne_Q2)))
  · exact hF.congr' hev.symm

end Work.Drive
