import Mathlib

namespace Work.FIChain

/-- The interval integral over `a..b` of the indicator of `Set.Iio t` (with `a ≤ t ≤ b`)
collapses to the interval integral over `a..t`.  Since interval integrals are Lebesgue
integrals, the two sets `Iio t ∩ Ioc a b` and `Ioc a t` agree up to the null set `{t}`. -/
theorem s3swap_indicator_integral (g : ℝ → ℝ) {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    ∫ u in a..b, (Set.Iio t).indicator (fun u => g u / u) u = ∫ u in a..t, g u / u := by
  -- On `Ioc a b`, the half-line `Iio t` cuts out exactly `Ioo a t` (up to the point `t`).
  have hIoc : Set.Ioc a b ∩ Set.Iio t = Set.Ioo a t := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, le_trans (le_of_lt h3) htb⟩, h3⟩
  -- `Ioo a t` and `Ioc a t` differ only by the null set `{t}`.
  have hae : Set.Ioo a t =ᵐ[MeasureTheory.volume] Set.Ioc a t := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have : Set.Ioo a t \ Set.Ioc a t = ∅ :=
        Set.sdiff_eq_empty.mpr Set.Ioo_subset_Ioc_self
      rw [this, MeasureTheory.measure_empty]
    · refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton t)
      intro u hu
      simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff] at hu ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hu
      by_contra hne
      exact h3 ⟨h1, lt_of_le_of_ne h2 hne⟩
  rw [intervalIntegral.integral_of_le (le_trans hat htb), intervalIntegral.integral_of_le hat,
      MeasureTheory.setIntegral_indicator measurableSet_Iio, hIoc,
      MeasureTheory.setIntegral_congr_set hae]

end Work.FIChain
