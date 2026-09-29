import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory

/-- Auxiliary: the one-dimensional logarithmic kernel
`t ↦ max (log (ρ / |t - s|)) 0` is integrable with respect to Lebesgue measure, for every
scale `ρ > 0`.  The kernel is supported on the interval `[s - ρ, s + ρ]`, on which it agrees
with `log ρ - log |t - s|`, and `log |·|` is interval integrable. -/
private lemma logKernel_translate_integrable {ρ s : ℝ} (hρ : 0 < ρ) :
    MeasureTheory.Integrable (fun t : ℝ => max (Real.log (ρ / |t - s|)) 0)
      MeasureTheory.volume := by
  have hle : s - ρ ≤ s + ρ := by linarith
  -- Away from the single point `s`, `log (ρ/|t-s|)` is `log ρ - log |t-s|`.
  have hs_ne :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc (s - ρ) (s + ρ))), t ≠ s := by
    rw [MeasureTheory.ae_iff]
    have h : {t : ℝ | ¬ t ≠ s} = {s} := by ext t; simp
    rw [h, MeasureTheory.Measure.restrict_apply (MeasurableSet.singleton s)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton s)
  -- `log |·|` is interval integrable on `[-ρ, ρ]`.
  have h1 : IntervalIntegrable (fun u : ℝ => Real.log |u|) MeasureTheory.volume (-ρ) ρ := by
    simpa only [Real.log_abs] using
      intervalIntegral.intervalIntegrable_log' (a := -ρ) (b := ρ)
  -- Shift to `[s - ρ, s + ρ]`.
  have h2 : IntervalIntegrable (fun t : ℝ => Real.log |t - s|) MeasureTheory.volume
      (s - ρ) (s + ρ) := by
    have h := h1.comp_sub_right s
    rw [show -ρ + s = s - ρ by ring, show ρ + s = s + ρ by ring] at h
    exact h
  -- Subtract from the constant `log ρ`.
  have h3 : IntervalIntegrable (fun t : ℝ => Real.log ρ - Real.log |t - s|)
      MeasureTheory.volume (s - ρ) (s + ρ) :=
    IntervalIntegrable.sub (intervalIntegrable_const (c := Real.log ρ)) h2
  have h4 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.log ρ - Real.log |t - s|)
      (Set.Ioc (s - ρ) (s + ρ)) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp h3
  -- Replace by `log (ρ / |t - s|)`.
  have h5 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.log (ρ / |t - s|))
      (Set.Ioc (s - ρ) (s + ρ)) MeasureTheory.volume := by
    refine h4.congr_fun_ae ?_
    filter_upwards [hs_ne] with t ht
    rw [Real.log_div (ne_of_gt hρ) (abs_ne_zero.mpr (sub_ne_zero.mpr ht))]
  -- Replace by the `max` with `0`.
  have h6 : MeasureTheory.IntegrableOn (fun t : ℝ => max (Real.log (ρ / |t - s|)) 0)
      (Set.Ioc (s - ρ) (s + ρ)) MeasureTheory.volume := by
    refine h5.congr_fun ?_ measurableSet_Ioc
    intro t ht
    show Real.log (ρ / |t - s|) = max (Real.log (ρ / |t - s|)) 0
    rw [Set.mem_Ioc] at ht
    have habs : |t - s| ≤ ρ := by
      rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    by_cases hts : t - s = 0
    · rw [hts]; simp
    · have hpos : 0 < |t - s| := abs_pos.mpr hts
      have hge : 1 ≤ ρ / |t - s| := (one_le_div hpos).mpr habs
      exact (max_eq_left (Real.log_nonneg hge)).symm
  -- The kernel vanishes off the interval.
  exact h6.integrable_of_forall_notMem_eq_zero (fun x hx => by
    show max (Real.log (ρ / |x - s|)) 0 = 0
    rw [Set.mem_Ioc] at hx
    rw [not_and_or, not_lt, not_le] at hx
    have habs : ρ ≤ |x - s| := by
      rcases hx with hx | hx
      · rw [abs_of_nonpos (by linarith : x - s ≤ 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x - s)]; linarith
    have hpos : 0 < |x - s| := lt_of_lt_of_le hρ habs
    have hle1 : ρ / |x - s| ≤ 1 := (div_le_one hpos).mpr habs
    exact max_eq_right (Real.log_nonpos (div_nonneg hρ.le (abs_nonneg _)) hle1))

theorem rcNormKernel_integrable (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    MeasureTheory.Integrable (fun t : ℝ => max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0)
      MeasureTheory.volume := by
  -- For `t ≠ z.re` the norm `‖z - t‖` is at least `|t - z.re|`, so `log (ρ/‖z-t‖) ≤
  -- log (ρ/|t - z.re|)`; the point `z.re` is null.
  have hae_ne : ∀ᵐ t : ℝ ∂(MeasureTheory.volume), t ≠ z.re := by
    rw [MeasureTheory.ae_iff]
    have h : {t : ℝ | ¬ t ≠ z.re} = {z.re} := by ext t; simp
    rw [h]
    exact measure_singleton z.re
  have hg : MeasureTheory.Integrable (fun t : ℝ => max (Real.log (ρ / |t - z.re|)) 0)
      MeasureTheory.volume := logKernel_translate_integrable (s := z.re) hρ
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0) MeasureTheory.volume := by
    apply Measurable.aestronglyMeasurable
    have hz1 : Measurable (fun t : ℝ => z - (t:ℂ)) :=
      measurable_const.sub Complex.continuous_ofReal.measurable
    have hz2 : Measurable (fun t : ℝ => ‖z - (t:ℂ)‖) := hz1.norm
    have hz3 : Measurable (fun t : ℝ => ρ / ‖z - (t:ℂ)‖) := measurable_const.div hz2
    exact (hz3.log).max measurable_const
  refine hg.mono' hmeas ?_
  filter_upwards [hae_ne] with t ht
  have hfnn : 0 ≤ max (Real.log (ρ / ‖z - (t:ℂ)‖)) 0 := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hne : t - z.re ≠ 0 := sub_ne_zero.mpr ht
  have hpos : 0 < |t - z.re| := abs_pos.mpr hne
  have hle_norm : |t - z.re| ≤ ‖z - (t:ℂ)‖ := by
    have h1 := Complex.abs_re_le_norm (z - (t:ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h1
    rw [abs_sub_comm] at h1
    exact h1
  have hposnorm : 0 < ‖z - (t:ℂ)‖ := lt_of_lt_of_le hpos hle_norm
  have hdiv : ρ / ‖z - (t:ℂ)‖ ≤ ρ / |t - z.re| :=
    div_le_div_of_nonneg_left hρ.le hpos hle_norm
  have hlog : Real.log (ρ / ‖z - (t:ℂ)‖) ≤ Real.log (ρ / |t - z.re|) :=
    Real.log_le_log (div_pos hρ hposnorm) hdiv
  exact max_le (le_trans hlog (le_max_left _ _)) (le_max_right _ _)

end Work.TMComp.RealCartan
