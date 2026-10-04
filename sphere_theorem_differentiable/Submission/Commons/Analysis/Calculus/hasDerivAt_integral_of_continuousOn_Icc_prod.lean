import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set
open scoped Topology MeasureTheory Interval

namespace Commons.Analysis.Calculus

/-- **Differentiation under the integral sign on a compact rectangle**, in the form needed by
second-variation arguments: if `g` and its `s`-derivative `g'` are continuous on the rectangle
`[-d,d] × [a,b]` and `g'` is the pointwise `s`-derivative of `g` on the interior of the `s`-interval,
then `s ↦ ∫_a^b g(s,t) dt` is differentiable at `0` with derivative `∫_a^b g'(0,t) dt`.

No domination or measurability hypotheses are needed: compactness of the rectangle plus continuity
supply them (the proof goes through Fubini for interval integrals and the fundamental result of
calculus). -/
theorem hasDerivAt_integral_of_continuousOn_Icc_prod
    {g g' : ℝ → ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hg' : ContinuousOn (fun p : ℝ × ℝ => g' p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc a b, HasDerivAt (fun σ' : ℝ => g σ' t) (g' σ t) σ) :
    HasDerivAt (fun σ : ℝ => ∫ t in a..b, g σ t) (∫ t in a..b, g' 0 t) 0 := by
  have hmem : (0:ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have h0 : (0:ℝ) ∈ Set.Icc (-δ) δ := ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  -- Continuity of the slices `t ↦ g x t` on the `t`-interval, for `x` in the `s`-interval.
  have sliceCont : ∀ x ∈ Set.Icc (-δ) δ, ContinuousOn (fun t : ℝ => g x t) (Set.Icc a b) := by
    intro x hx
    have h1 : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc a b) :=
      ((continuous_const : Continuous fun _ : ℝ => x).prodMk continuous_id).continuousOn
    have h2 := hg.comp h1 (fun t ht => ⟨hx, ht⟩)
    convert h2 using 1
    ext t; rfl
  have sliceCont' : ∀ x ∈ Set.Icc (-δ) δ, ContinuousOn (fun t : ℝ => g' x t) (Set.Icc a b) := by
    intro x hx
    have h1 : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc a b) :=
      ((continuous_const : Continuous fun _ : ℝ => x).prodMk continuous_id).continuousOn
    have h2 := hg'.comp h1 (fun t ht => ⟨hx, ht⟩)
    convert h2 using 1
    ext t; rfl
  -- Measurability of the integrands, from continuity of the slices.
  have hF_meas : ∀ᶠ x in 𝓝 (0:ℝ),
      AEStronglyMeasurable (fun t : ℝ => g x t) (volume.restrict (Ι a b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with x hx
    exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact
      (sliceCont x ⟨le_of_lt hx.1, le_of_lt hx.2⟩) isCompact_Icc measurableSet_uIoc
      (by rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self)
  have hF_int : IntervalIntegrable (fun t : ℝ => g 0 t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (sliceCont 0 h0)
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => g' 0 t) (volume.restrict (Ι a b)) :=
    ContinuousOn.aestronglyMeasurable_of_subset_isCompact
      (sliceCont' 0 h0) isCompact_Icc measurableSet_uIoc
      (by rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self)
  -- A uniform bound on `‖g'‖` over the compact rectangle supplies the domination hypothesis.
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc (a := -δ) (b := δ)).prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn hg'
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ Set.Ioo (-δ) δ, ‖g' x t‖ ≤ C := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hab] at ht
    exact hC (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  -- The pointwise derivative hypothesis, available for all `t` in the interval.
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ Set.Ioo (-δ) δ,
      HasDerivAt (fun x => g x t) (g' x t) x := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le hab] at ht
    exact hderiv x hx t ⟨le_of_lt ht.1, ht.2⟩
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => g x t) (F' := fun x t => g' x t)
    (s := Set.Ioo (-δ) δ) (bound := fun _ => C)
    (isOpen_Ioo.mem_nhds hmem) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

end Commons.Analysis.Calculus