import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set intervalIntegral Filter
open scoped Interval Topology

namespace Commons.Analysis.Calculus

/-- Continuity of a slice `t ↦ f x t` on `[a,b]` if `f` is continuous on the compact
rectangle `[-δ,δ] × [a,b]` and `x ∈ [-δ,δ]`. -/
private lemma continuousOn_slice_of_prod_Icc {f : ℝ → ℝ → ℝ} {δ a b : ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    {x : ℝ} (hx : x ∈ Set.Icc (-δ) δ) :
    ContinuousOn (fun t => f x t) (Set.Icc a b) :=
  ContinuousOn.comp' (g := fun p : ℝ × ℝ => f p.1 p.2) (f := fun t : ℝ => (x, t))
    (s := Set.Icc a b) (t := Set.Icc (-δ) δ ×ˢ Set.Icc a b) hf
    ((continuous_const.prodMk continuous_id).continuousOn)
    (fun _ ht => ⟨hx, ht⟩)

/-- A continuous function on the compact rectangle is uniformly bounded by a constant. -/
private lemma exists_norm_bound_of_prod_Icc {f : ℝ → ℝ → ℝ} {δ a b : ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b)) :
    ∃ C, ∀ x ∈ Set.Icc (-δ) δ, ∀ t ∈ Set.Icc a b, ‖f x t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => ‖f p.1 p.2‖)
      (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
  exact ⟨C, fun x hx t ht => by simpa using hC (x, t) ⟨hx, ht⟩⟩

/-- Slices of a function continuous on the rectangle are interval integrable. -/
private lemma intervalIntegrable_slice_of_prod_Icc {f : ℝ → ℝ → ℝ} {δ a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    {x : ℝ} (hx : x ∈ Set.Icc (-δ) δ) :
    IntervalIntegrable (fun t => f x t) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab
    (continuousOn_slice_of_prod_Icc hf hx)

/-- Slices of a function continuous on the rectangle are a.e. strongly measurable. -/
private lemma aestronglyMeasurable_slice_of_prod_Icc {f : ℝ → ℝ → ℝ} {δ a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    {x : ℝ} (hx : x ∈ Set.Icc (-δ) δ) :
    AEStronglyMeasurable (fun t => f x t) (volume.restrict (Ι a b)) :=
  (intervalIntegrable_iff.1 (intervalIntegrable_slice_of_prod_Icc hab hf hx)).aestronglyMeasurable

/-- `Ι a b ⊆ [a,b]` when `a ≤ b`. -/
private lemma uIoc_subset_Icc {a b : ℝ} (hab : a ≤ b) : Ι a b ⊆ Set.Icc a b := by
  rw [← Set.uIcc_of_le hab]
  exact Set.uIoc_subset_uIcc

/-- **The second derivative under the integral sign on a compact rectangle.**  If `g`, `g'` and `g''`
are continuous on `[-δ,δ] × [a,b]`, `g'` is the `s`-derivative of `g` and `g''` the `s`-derivative of
`g'` pointwise on the rectangle, then `s ↦ ∫_a^b g(s,t) dt` is twice differentiable at `0` with
second derivative `∫_a^b g''(0,t) dt`.

This is the analytic engine of every second-variation computation: it says that the second derivative
of the energy is the integral of the pointwise second derivative of the integrand. -/
theorem hasDerivAt_deriv_integral_of_continuousOn_Icc_prod
    {g g' g'' : ℝ → ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hg' : ContinuousOn (fun p : ℝ × ℝ => g' p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hg'' : ContinuousOn (fun p : ℝ × ℝ => g'' p.1 p.2) (Set.Icc (-δ) δ ×ˢ Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc a b, HasDerivAt (fun σ' : ℝ => g σ' t) (g' σ t) σ)
    (hderiv' : ∀ σ ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc a b, HasDerivAt (fun σ' : ℝ => g' σ' t) (g'' σ t) σ) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in a..b, g σ t)) (∫ t in a..b, g'' 0 t) 0 := by
  have hneg : (-δ : ℝ) < 0 := by linarith
  have hpos : (0 : ℝ) < δ := hδ
  have hs_nhds : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds hneg hpos
  have hIoc : Ι a b ⊆ Set.Icc a b := uIoc_subset_Icc hab
  obtain ⟨C', hC'⟩ := exists_norm_bound_of_prod_Icc hg'
  obtain ⟨C'', hC''⟩ := exists_norm_bound_of_prod_Icc hg''
  -- ### Step A: `σ ↦ ∫ g'(σ,t)` is differentiable at `0` with derivative `∫ g''(0,t)`
  have hA_meas : ∀ᶠ x in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (fun t => g' x t) (volume.restrict (Ι a b)) := by
    filter_upwards [hs_nhds] with x hx
    exact aestronglyMeasurable_slice_of_prod_Icc hab hg' (Ioo_subset_Icc_self hx)
  have hA_int : IntervalIntegrable (fun t => g' 0 t) volume a b :=
    intervalIntegrable_slice_of_prod_Icc hab hg' (⟨hneg.le, hpos.le⟩ : (0:ℝ) ∈ Set.Icc (-δ) δ)
  have hA'_meas : AEStronglyMeasurable (fun t => g'' 0 t) (volume.restrict (Ι a b)) :=
    aestronglyMeasurable_slice_of_prod_Icc hab hg'' (⟨hneg.le, hpos.le⟩ : (0:ℝ) ∈ Set.Icc (-δ) δ)
  have hA_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      ∀ x ∈ Set.Ioo (-δ) δ, ‖g'' x t‖ ≤ C'' := by
    filter_upwards with t ht x hx
    exact hC'' x (Ioo_subset_Icc_self hx) t (hIoc ht)
  have hA_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      ∀ x ∈ Set.Ioo (-δ) δ, HasDerivAt (fun x : ℝ => g' x t) (g'' x t) x := by
    filter_upwards with t ht x hx
    exact hderiv' x hx t (hIoc ht)
  have hA := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun σ t => g' σ t) (F' := fun σ t => g'' σ t) (x₀ := 0)
    (s := Set.Ioo (-δ) δ) (bound := fun _ => C'') (μ := volume)
    hs_nhds hA_meas hA_int hA'_meas hA_bound intervalIntegrable_const hA_diff)
  -- ### Step B: `σ ↦ ∫ g(σ,t)` is differentiable on a neighbourhood of `0`, derivative `∫ g'(σ,t)`
  have hB : ∀ σ ∈ Set.Ioo (-δ) δ,
      HasDerivAt (fun σ' : ℝ => ∫ t in a..b, g σ' t) (∫ t in a..b, g' σ t) σ := by
    intro σ hσ
    have hsσ : Set.Ioo (-δ) δ ∈ 𝓝 σ := Ioo_mem_nhds hσ.1 hσ.2
    have hB_meas : ∀ᶠ x in 𝓝 σ,
        AEStronglyMeasurable (fun t => g x t) (volume.restrict (Ι a b)) := by
      filter_upwards [hsσ] with x hx
      exact aestronglyMeasurable_slice_of_prod_Icc hab hg (Ioo_subset_Icc_self hx)
    have hB_int : IntervalIntegrable (fun t => g σ t) volume a b :=
      intervalIntegrable_slice_of_prod_Icc hab hg (Ioo_subset_Icc_self hσ)
    have hB'_meas : AEStronglyMeasurable (fun t => g' σ t) (volume.restrict (Ι a b)) :=
      aestronglyMeasurable_slice_of_prod_Icc hab hg' (Ioo_subset_Icc_self hσ)
    have hB_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
        ∀ x ∈ Set.Ioo (-δ) δ, ‖g' x t‖ ≤ C' := by
      filter_upwards with t ht x hx
      exact hC' x (Ioo_subset_Icc_self hx) t (hIoc ht)
    have hB_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
        ∀ x ∈ Set.Ioo (-δ) δ, HasDerivAt (fun x : ℝ => g x t) (g' x t) x := by
      filter_upwards with t ht x hx
      exact hderiv x hx t (hIoc ht)
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun σ t => g σ t) (F' := fun σ t => g' σ t) (x₀ := σ)
      (s := Set.Ioo (-δ) δ) (bound := fun _ => C') (μ := volume)
      hsσ hB_meas hB_int hB'_meas hB_bound intervalIntegrable_const hB_diff).2
  -- ### Conclusion: `deriv F` agrees with `σ ↦ ∫ g'(σ,t)` near `0`
  have h_eq : (fun σ : ℝ => deriv (fun σ' : ℝ => ∫ t in a..b, g σ' t) σ)
      =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => ∫ t in a..b, g' σ t) := by
    filter_upwards [hs_nhds] with σ hσ
    exact (hB σ hσ).deriv
  exact hA.2.congr_of_eventuallyEq h_eq

end Commons.Analysis.Calculus