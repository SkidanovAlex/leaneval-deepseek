import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Submission.Commons.Analysis.Calculus.hasDerivAt_integral_of_continuousOn_Icc_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Calculus

open MeasureTheory Filter Set
open scoped Topology MeasureTheory Interval

/-- **Differentiation under the integral sign on a compact rectangle, at an interior point.**

This is the pointwise version of
`Commons.Analysis.Calculus.hasDerivAt_integral_of_continuousOn_Icc_prod`: if `g` and its
`s`-derivative `g'` are continuous on the rectangle `[-d,d] × [a,b]` and `g'` is the pointwise
`s`-derivative of `g` on the interior of the `s`-interval, then for every interior point `x` the
map `s ↦ ∫_a^b g(s,t) dt` is differentiable at `x` with derivative `∫_a^b g'(x,t) dt`.

No domination or measurability hypotheses are needed: compactness of the rectangle plus continuity
supply them (via Mathlib's parametric interval-integral differentiation lemma). -/
theorem hasDerivAt_integral_of_continuousOn_Icc_prod_at
    {g g' : ℝ → ℝ → ℝ} {a b δ x : ℝ} (hab : a ≤ b) (_hδ : 0 < δ)
    (hx : x ∈ Set.Ioo (-δ) δ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hg' : ContinuousOn (fun p : ℝ × ℝ => g' p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun σ' : ℝ => g σ' t) (g' σ t) σ) :
    HasDerivAt (fun σ : ℝ => ∫ t in a..b, g σ t) (∫ t in a..b, g' x t) x := by
  have hxIcc : x ∈ Set.Icc (-δ) δ := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- Continuity of the slices `t ↦ g s t` on the `t`-interval, for `s` in the `s`-interval.
  have sliceCont : ∀ y ∈ Set.Icc (-δ) δ, ContinuousOn (fun t : ℝ => g y t) (Set.Icc a b) := by
    intro y hy
    have h1 : ContinuousOn (fun t : ℝ => (y, t)) (Set.Icc a b) :=
      ((continuous_const : Continuous fun _ : ℝ => y).prodMk continuous_id).continuousOn
    have h2 := hg.comp h1 (fun t ht => ⟨hy, ht⟩)
    convert h2 using 1
    ext t; rfl
  have sliceCont' : ∀ y ∈ Set.Icc (-δ) δ, ContinuousOn (fun t : ℝ => g' y t) (Set.Icc a b) := by
    intro y hy
    have h1 : ContinuousOn (fun t : ℝ => (y, t)) (Set.Icc a b) :=
      ((continuous_const : Continuous fun _ : ℝ => y).prodMk continuous_id).continuousOn
    have h2 := hg'.comp h1 (fun t ht => ⟨hy, ht⟩)
    convert h2 using 1
    ext t; rfl
  -- Measurability of the integrands, from continuity of the slices.
  have hF_meas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun t : ℝ => g y t) (volume.restrict (Ι a b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact
      (sliceCont y ⟨le_of_lt hy.1, le_of_lt hy.2⟩) isCompact_Icc measurableSet_uIoc
      (by rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self)
  have hF_int : IntervalIntegrable (fun t : ℝ => g x t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (sliceCont x hxIcc)
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => g' x t) (volume.restrict (Ι a b)) :=
    ContinuousOn.aestronglyMeasurable_of_subset_isCompact
      (sliceCont' x hxIcc) isCompact_Icc measurableSet_uIoc
      (by rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self)
  -- A uniform bound on `‖g'‖` over the compact rectangle supplies the domination hypothesis.
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc (a := -δ) (b := δ)).prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn hg'
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ y ∈ Set.Ioo (-δ) δ, ‖g' y t‖ ≤ C := by
    filter_upwards with t ht y hy
    rw [Set.uIoc_of_le hab] at ht
    exact hC (y, t) ⟨⟨le_of_lt hy.1, le_of_lt hy.2⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  -- The pointwise derivative hypothesis, available for all `t` in the interval.
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ y ∈ Set.Ioo (-δ) δ,
      HasDerivAt (fun y => g y t) (g' y t) y := by
    filter_upwards with t ht y hy
    rw [Set.uIoc_of_le hab] at ht
    exact hderiv y hy t ⟨le_of_lt ht.1, ht.2⟩
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t => g y t) (F' := fun y t => g' y t)
    (s := Set.Ioo (-δ) δ) (bound := fun _ => C)
    (isOpen_Ioo.mem_nhds hx) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

open MeasureTheory Filter Set in
open scoped Topology MeasureTheory Interval in
theorem eventually_differentiableAt_integral_of_continuousOn
    {g g' : ℝ → ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hg' : ContinuousOn (fun p : ℝ × ℝ => g' p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun σ' : ℝ => g σ' t) (g' σ t) σ) :
    ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ => ∫ t in a..b, g σ t) σ := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  filter_upwards [isOpen_Ioo.mem_nhds h0] with σ hσ
  exact (hasDerivAt_integral_of_continuousOn_Icc_prod_at hab hδ hσ hg hg' hderiv).differentiableAt

end Commons.Analysis.Calculus