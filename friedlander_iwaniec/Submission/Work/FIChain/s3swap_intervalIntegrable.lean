import Mathlib

namespace Work.FIChain

open MeasureTheory

/-- The step function `u ↦ (Iio t).indicator (fun u => h u / u) u` is interval integrable on
`[a,b]` as soon as `1 ≤ a ≤ b`, `h` is measurable and bounded by `M`: on `(a,b]` one has `u ≥ 1`,
so `|h u / u| ≤ |h u| ≤ M`, and the indicator only shrinks that. -/
theorem s3swap_intervalIntegrable (h : ℝ → ℝ) (M : ℝ) {a b t : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hmeas : Measurable h) (hbdd : ∀ u, |h u| ≤ M) :
    IntervalIntegrable (fun u => (Set.Iio t).indicator (fun u => h u / u) u) volume a b := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (h 0)) (hbdd 0)
  have hmeas' : Measurable (fun u : ℝ => (Set.Iio t).indicator (fun u => h u / u) u) :=
    (hmeas.div measurable_id).indicator measurableSet_Iio
  constructor
  · refine Measure.integrableOn_of_bounded
      (s_finite := (measure_Ioc_lt_top (a := a) (b := b)).ne)
      (f_mble := hmeas'.aestronglyMeasurable) (M := M) ?_
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u hu
    have hu1 : 1 ≤ u := le_trans ha (le_of_lt hu.1)
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    rw [Real.norm_eq_abs]
    have hle : |(Set.Iio t).indicator (fun u => h u / u) u| ≤ |h u / u| := by
      by_cases hlt : u ∈ Set.Iio t
      · rw [Set.indicator_of_mem hlt]
      · rw [Set.indicator_of_notMem hlt, abs_zero]
        exact abs_nonneg _
    calc |(Set.Iio t).indicator (fun u => h u / u) u|
        ≤ |h u / u| := hle
      _ = |h u| / u := by rw [abs_div, abs_of_pos hu0]
      _ ≤ M := by
          rw [div_le_iff₀ hu0]
          calc |h u| ≤ M := hbdd u
            _ = M * 1 := (mul_one M).symm
            _ ≤ M * u := mul_le_mul_of_nonneg_left hu1 hM
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact integrableOn_empty

end Work.FIChain
