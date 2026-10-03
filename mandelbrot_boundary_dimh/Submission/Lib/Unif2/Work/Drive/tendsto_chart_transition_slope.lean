import Mathlib

/-!
# The slope of a chart transition tends to its derivative

For a one-dimensional complex manifold `X` (a Riemann surface, here only a `C¹` manifold
modelled on `ℂ`), the transition map between the chart at `x` and the chart at `y`,
`(chartAt ℂ x).symm.trans (chartAt ℂ y)`, is holomorphic, and the difference quotient of the
coordinate change, written in terms of the two charts, converges to its derivative.

This is the "chain rule on the overlap of two charts" fact used when rewriting derivatives of
functions expressed in different charts.
-/

open scoped Manifold Topology

open Set Filter

open scoped Topology

namespace Work.Drive

theorem tendsto_chart_transition_slope {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x y : X} (hy : y ∈ (chartAt ℂ x).source) :
    Filter.Tendsto (fun z : X =>
        ((chartAt ℂ y) z - (chartAt ℂ y) y) / ((chartAt ℂ x) z - (chartAt ℂ x) y))
      (nhdsWithin y {y}ᶜ)
      (nhds (deriv ((chartAt ℂ x).symm.trans (chartAt ℂ y)) ((chartAt ℂ x) y))) := by
  -- the point `(chartAt ℂ x) y` lies in the source of the transition
  have hu : (chartAt ℂ x) y ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨(chartAt ℂ x).map_source hy, ?_⟩
    show (chartAt ℂ x).symm ((chartAt ℂ x) y) ∈ (chartAt ℂ y).source
    rw [OpenPartialHomeomorph.left_inv _ hy]
    exact mem_chart_source ℂ y
  -- the transition is holomorphic (it is `C¹` as a map of complex manifolds)
  have hCD : ContDiffOn ℂ 1 (↑((chartAt ℂ x).symm.trans (chartAt ℂ y)))
      ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) 1
        (↑(chartAt ℂ y)) (chartAt ℂ y).source := contMDiffOn_chart
    have h2 : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) 1
        (↑(chartAt ℂ x).symm) ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source :=
      (contMDiffOn_chart_symm (x := x)).mono inter_subset_left
    have hst : ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source ⊆
        (↑(chartAt ℂ x).symm) ⁻¹' (chartAt ℂ y).source := by
      rw [OpenPartialHomeomorph.trans_source]; exact inter_subset_right
    have h3 : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) 1
        (↑(chartAt ℂ y) ∘ ↑(chartAt ℂ x).symm) ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source :=
      ContMDiffOn.comp h1 h2 hst
    have h4 := h3.contDiffOn
    rw [funext (fun w =>
      OpenPartialHomeomorph.trans_apply (chartAt ℂ x).symm (chartAt ℂ y) (x := w))]
    exact h4
  have hda : DifferentiableAt ℂ (↑((chartAt ℂ x).symm.trans (chartAt ℂ y))) ((chartAt ℂ x) y) := by
    have hdw : DifferentiableWithinAt ℂ (↑((chartAt ℂ x).symm.trans (chartAt ℂ y)))
        ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source ((chartAt ℂ x) y) :=
      (hCD.contDiffWithinAt hu).differentiableWithinAt (by norm_num)
    exact hdw.differentiableAt (((chartAt ℂ x).symm.trans (chartAt ℂ y)).open_source.mem_nhds hu)
  have hderiv : HasDerivAt (↑((chartAt ℂ x).symm.trans (chartAt ℂ y)))
      (deriv (↑((chartAt ℂ x).symm.trans (chartAt ℂ y))) ((chartAt ℂ x) y)) ((chartAt ℂ x) y) :=
    hda.hasDerivAt
  -- the chart at `x` sends the punctured neighbourhood of `y` to the punctured neighbourhood of
  -- its value
  have hφ : Filter.Tendsto (fun z : X => (chartAt ℂ x) z) (𝓝[≠] y) (𝓝[≠] ((chartAt ℂ x) y)) := by
    have hcont : ContinuousAt (↑(chartAt ℂ x) : X → ℂ) y :=
      (chartAt ℂ x).continuousOn.continuousAt ((chartAt ℂ x).open_source.mem_nhds hy)
    rw [nhdsWithin, nhdsWithin, Filter.tendsto_inf]
    refine ⟨hcont.tendsto.mono_left inf_le_left, ?_⟩
    rw [Filter.tendsto_principal]
    refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds ((chartAt ℂ x).open_source.mem_nhds hy))) ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz1 ⊢
    exact fun hcon => hz1 ((chartAt ℂ x).injOn hz2 hy hcon)
  -- finish: the difference quotient is the slope of the transition composed with the chart
  refine Filter.Tendsto.congr' ?_ (hderiv.tendsto_slope.comp hφ)
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨(chartAt ℂ x).source, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds ((chartAt ℂ x).open_source.mem_nhds hy)
  · intro z hz
    simp only [Function.comp_apply]
    rw [slope_def_field, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.left_inv _ hz, OpenPartialHomeomorph.left_inv _ hy]

end Work.Drive
