import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

namespace Commons.Analysis.Calculus

open MeasureTheory Set
open scoped Topology Interval

theorem intervalIntegral_hasDerivAt_of_continuousOn_uIcc
    {F F' : ℝ → ℝ → ℝ} {s₀ a b s₁ s₂ : ℝ} (h₁ : s₁ < s₀) (h₂ : s₀ < s₂)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc s₁ s₂ ×ˢ Set.uIcc a b))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Set.Icc s₁ s₂ ×ˢ Set.uIcc a b))
    (hd : ∀ s ∈ Set.Icc s₁ s₂, ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u => F u t) (F' s t) s) :
    HasDerivAt (fun s => ∫ t in a..b, F s t) (∫ t in a..b, F' s₀ t) s₀ := by
  set K : Set (ℝ × ℝ) := Set.Icc s₁ s₂ ×ˢ Set.uIcc a b with hK
  have hKcompact : IsCompact K := by
    rw [hK]; exact isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hF'
  have hs₀ : s₀ ∈ Set.Icc s₁ s₂ := ⟨le_of_lt h₁, le_of_lt h₂⟩
  have hmaps : ∀ x ∈ Set.Icc s₁ s₂, Set.MapsTo (fun t : ℝ => (x, t)) (Set.uIcc a b) K :=
    fun x hx t ht => by rw [hK]; exact ⟨hx, ht⟩
  have hcontF : ∀ x ∈ Set.Icc s₁ s₂, ContinuousOn (fun t => F x t) (Set.uIcc a b) := fun x hx =>
    (hF.comp (continuous_const.prodMk continuous_id).continuousOn (hmaps x hx)).congr
      (fun t _ => rfl)
  have hcontF' : ∀ x ∈ Set.Icc s₁ s₂, ContinuousOn (fun t => F' x t) (Set.uIcc a b) := fun x hx =>
    (hF'.comp (continuous_const.prodMk continuous_id).continuousOn (hmaps x hx)).congr
      (fun t _ => rfl)
  have hF_meas : ∀ᶠ x in 𝓝 s₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    filter_upwards [Icc_mem_nhds h₁ h₂] with x hx
    exact ((hcontF x hx).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (F s₀) volume a b :=
    (hcontF s₀ hs₀).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ι a b)) :=
    ((hcontF' s₀ hs₀).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ Set.Icc s₁ s₂, ‖F' x t‖ ≤ C := by
    filter_upwards with t ht x hx
    simpa using hC (x, t) (by rw [hK]; exact ⟨hx, uIoc_subset_uIcc ht⟩)
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b →
      ∀ x ∈ Set.Icc s₁ s₂, HasDerivAt (fun u => F u t) (F' x t) x := by
    filter_upwards with t ht x hx
    exact hd x hx t (uIoc_subset_uIcc ht)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (bound := fun _ : ℝ => C)
    (F := F) (F' := F') (x₀ := s₀) (s := Set.Icc s₁ s₂)
    (Icc_mem_nhds h₁ h₂) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa using key.2

end Commons.Analysis.Calculus