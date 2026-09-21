import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

namespace Commons.Analysis.Calculus

open MeasureTheory Set
open scoped Topology Interval

theorem intervalIntegral_hasDerivAt_of_continuousOn_of_le
    {F F' : ℝ → ℝ → ℝ} {s₀ a b s₁ s₂ : ℝ} (h₁ : s₁ < s₀) (h₂ : s₀ < s₂) (hab : a ≤ b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc s₁ s₂ ×ˢ Set.Icc a b))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Set.Icc s₁ s₂ ×ˢ Set.Icc a b))
    (hd : ∀ s ∈ Set.Icc s₁ s₂, ∀ t ∈ Set.Icc a b, HasDerivAt (fun u => F u t) (F' s t) s) :
    HasDerivAt (fun s => ∫ t in a..b, F s t) (∫ t in a..b, F' s₀ t) s₀ := by
  have hbox_compact : IsCompact (Set.Icc s₁ s₂ ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hbox_compact.exists_bound_of_continuousOn
    (continuous_norm.comp_continuousOn hF')
  have hM' : ∀ x ∈ Set.Icc s₁ s₂, ∀ t ∈ Set.Icc a b, ‖F' x t‖ ≤ M := by
    intro x hx t ht
    simpa using hM (x, t) ⟨hx, ht⟩
  have hsub : Ι a b ⊆ Set.Icc a b := by
    rw [← Set.uIcc_of_le hab]; exact Set.uIoc_subset_uIcc
  have hs₀ : s₀ ∈ Set.Ioo s₁ s₂ := ⟨h₁, h₂⟩
  have hcontF : ∀ x ∈ Set.Ioo s₁ s₂, ContinuousOn (fun t : ℝ => F x t) (Set.Icc a b) := by
    intro x hx
    exact hF.comp' (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨Set.Ioo_subset_Icc_self hx, ht⟩)
  have hcontF' : ∀ x ∈ Set.Ioo s₁ s₂, ContinuousOn (fun t : ℝ => F' x t) (Set.Icc a b) := by
    intro x hx
    exact hF'.comp' (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨Set.Ioo_subset_Icc_self hx, ht⟩)
  have hs : Set.Ioo s₁ s₂ ∈ 𝓝 s₀ := Ioo_mem_nhds h₁ h₂
  have hF_meas : ∀ᶠ x in 𝓝 s₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    filter_upwards [hs] with x hx
    exact ((hcontF x hx).mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (F s₀) volume a b :=
    (show ContinuousOn (fun t : ℝ => F s₀ t) ([[a, b]]) from by
      rw [Set.uIcc_of_le hab]; exact hcontF s₀ hs₀).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ι a b)) :=
    ((hcontF' s₀ hs₀).mono hsub).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      ∀ x ∈ Set.Ioo s₁ s₂, ‖F' x t‖ ≤ (fun _ : ℝ => M) t := by
    filter_upwards with t ht x hx
    exact hM' x (Set.Ioo_subset_Icc_self hx) t (hsub ht)
  have hbound_int : IntervalIntegrable (fun _ : ℝ => M) volume a b := intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      ∀ x ∈ Set.Ioo s₁ s₂, HasDerivAt (fun u : ℝ => F u t) (F' x t) x := by
    filter_upwards with t ht x hx
    exact hd x (Set.Ioo_subset_Icc_self hx) t (hsub ht)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := ℝ) (F := F) (F' := F') (x₀ := s₀)
    (s := Set.Ioo s₁ s₂) (a := a) (b := b) (bound := fun _ : ℝ => M)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact h.2

end Commons.Analysis.Calculus