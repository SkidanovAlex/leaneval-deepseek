import Mathlib
import Submission.Work.Analysis.RiemannSurface.chart_transition_analytic
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# Derivatives of chart transitions between members of the maximal atlas

`Work.Drive.deriv_chart_transition_ne_zero` and `Work.Drive.tendsto_chart_transition_slope`
do the same job for the *preferred* charts `chartAt ℂ x`.  The construction of the global phase
(`Work.Drive.exists_continuous_singleZero_phase`) has to work with a *chosen* chart family
`c : ℕ → OpenPartialHomeomorph X ℂ` out of the maximal atlas — `ChartedSpace.chartAt` is arbitrary
chosen data and can be trapped (see the "CRITICAL TRAP" note in
`Submission/Work/Drive/exists_continuous_singleZero_phase.lean`).  This file provides the two
chart-family statements.

Both are instances of the single groupoid fact
`StructureGroupoid.compatible_of_mem_maximalAtlas`: the transition `c.symm ≫ₕ d` of two maximal
atlas charts lies in the `C¹`-groupoid (hence is `ContDiffOn ℂ 1` on its source), so it is complex
analytic at every interior point; being the germ of a local biholomorphism, its derivative there
does not vanish.
-/

open scoped Manifold ContDiff Topology
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The transition of two maximal-atlas charts lies in the `C¹`-groupoid. -/
theorem mem_groupoid_transition_of_mem {c d : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hd : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X) :
    (c.symm.trans d) ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
  StructureGroupoid.compatible_of_mem_maximalAtlas
    (G := contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)) hc hd

/-- The transition of two maximal-atlas charts is complex analytic on its source. -/
theorem contDiffOn_transition_of_mem {c d : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hd : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X) :
    ContDiffOn ℂ 1 ((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      (c.symm.trans d).source := by
  have h := (mem_groupoid_of_pregroupoid.mp (mem_groupoid_transition_of_mem hc hd)).1
  simpa [contDiffPregroupoid] using h

/-- **The derivative of a maximal-atlas transition does not vanish.** -/
theorem deriv_transition_ne_zero_of_mem {c d : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hd : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    {y : X} (hy : y ∈ c.source) (hy' : y ∈ d.source) :
    deriv ((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ) (c y) ≠ 0 := by
  have hmem : (c.symm.trans d) ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    mem_groupoid_transition_of_mem hc hd
  have hw : c y ∈ (c.symm.trans d).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨c.map_source hy, ?_⟩
    show c.symm (c y) ∈ d.source
    rw [c.left_inv hy]
    exact hy'
  have hana : AnalyticAt ℂ ((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ) (c y) := by
    have hcd := contDiffOn_transition_of_mem hc hd
    exact (hcd.differentiableOn one_ne_zero).analyticAt
      ((c.symm.trans d).open_source.mem_nhds hw)
  obtain ⟨r, hrpos, hrsub⟩ :=
    Metric.isOpen_iff.mp ((c.symm.trans d).open_source) _ hw
  have hinj : Set.InjOn (((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ))
      (Metric.ball (c y) r) :=
    ((c.symm.trans d).injOn).mono hrsub
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hrpos hana hinj

/-- **The slope of a maximal-atlas transition tends to its derivative.** -/
theorem tendsto_transition_slope_of_mem {c d : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hd : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    {y : X} (hy : y ∈ c.source) (hy' : y ∈ d.source) :
    Filter.Tendsto (fun z : X => (d z - d y) / (c z - c y))
      (nhdsWithin y {y}ᶜ)
      (nhds (deriv ((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ) (c y))) := by
  have hw : c y ∈ (c.symm.trans d).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨c.map_source hy, ?_⟩
    show c.symm (c y) ∈ d.source
    rw [c.left_inv hy]
    exact hy'
  have hana : AnalyticAt ℂ ((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ) (c y) := by
    have hcd := contDiffOn_transition_of_mem hc hd
    exact (hcd.differentiableOn one_ne_zero).analyticAt
      ((c.symm.trans d).open_source.mem_nhds hw)
  have hderiv : HasDerivAt (((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ))
      (deriv (((c.symm.trans d : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)) (c y)) (c y) :=
    hana.differentiableAt.hasDerivAt
  -- the transition sends the punctured neighbourhood of `y` to the punctured neighbourhood of `c y`
  have hφ : Filter.Tendsto (fun z : X => c z) (nhdsWithin y {y}ᶜ) (nhdsWithin (c y) {(c y)}ᶜ) := by
    have hcont : ContinuousAt (c : X → ℂ) y := c.continuousOn.continuousAt (c.open_source.mem_nhds hy)
    rw [nhdsWithin, nhdsWithin, Filter.tendsto_inf]
    refine ⟨hcont.tendsto.mono_left inf_le_left, ?_⟩
    rw [Filter.tendsto_principal]
    refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (c.open_source.mem_nhds hy))) ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz1 ⊢
    exact fun hcon => hz1 (c.injOn hz2 hy hcon)
  -- finish: the difference quotient is the slope of the transition, composed with `c`
  refine Filter.Tendsto.congr' ?_ (hderiv.tendsto_slope.comp hφ)
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (c.open_source.mem_nhds hy)] with z hz hcs
  simp only [Function.comp_apply]
  rw [slope_def_field, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
    c.left_inv hcs, c.left_inv hy]

end Work.Drive
