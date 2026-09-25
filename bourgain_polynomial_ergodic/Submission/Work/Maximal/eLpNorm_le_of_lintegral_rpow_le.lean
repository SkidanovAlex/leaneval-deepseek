import Mathlib

namespace Work.Maximal

/-- Auxiliary: from `X ≤ A^p * Y` conclude `X^(1/p) ≤ A * Y^(1/p)` in `ℝ≥0∞`, for `p > 0`. -/
private theorem rpow_one_div_le_mul {X Y : ENNReal} {A : ℝ} {p : ℝ} (hp : 0 < p)
    (h : X ≤ ENNReal.ofReal A ^ p * Y) :
    X ^ (1 / p) ≤ ENNReal.ofReal A * Y ^ (1 / p) := by
  calc X ^ (1 / p) ≤ (ENNReal.ofReal A ^ p * Y) ^ (1 / p) :=
        ENNReal.monotone_rpow_of_nonneg (by positivity) h
    _ = (ENNReal.ofReal A ^ p) ^ (1 / p) * Y ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal A * Y ^ (1 / p) := by
        rw [← ENNReal.rpow_mul, show p * (1 / p) = 1 by rw [mul_one_div, div_self hp.ne'],
          ENNReal.rpow_one]

/-- Conversion of a `∫⁻ ‖·‖ₑ^p`-bound into an `eLpNorm` bound at exponent `p > 0`: taking the
`p`-th root of both sides, using `(eLpNorm F q)^p = ∫⁻ F^p` for `q = ENNReal.ofReal p` (and
`eLpNorm (fun m => ‖f m‖ₑ) = eLpNorm f`). -/
theorem eLpNorm_le_of_lintegral_rpow_le {p : ℝ} (hp : 0 < p) {F : ℤ → ENNReal} {A : ℝ} (hA : 0 ≤ A)
    {w : ℤ → ℂ}
    (h : ∫⁻ m : ℤ, F m ^ p ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal A ^ p * ∫⁻ m : ℤ, ‖w m‖ₑ ^ p ∂MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm F (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm w (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) ≤ p := hp.le
  have hp_ne : p ≠ 0 := hp.ne'
  have hq_ne_zero : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hq_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne_zero hq_ne_top
      MeasureTheory.AEStronglyMeasurable.of_discrete,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne_zero hq_ne_top
      MeasureTheory.AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp0]
  simp only [enorm_eq_self]
  calc (∫⁻ m : ℤ, F m ^ p ∂MeasureTheory.Measure.count) ^ (1 / p)
      ≤ (ENNReal.ofReal A ^ p * ∫⁻ m : ℤ, ‖w m‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) :=
        ENNReal.monotone_rpow_of_nonneg (by positivity) h
    _ = (ENNReal.ofReal A ^ p) ^ (1 / p)
          * (∫⁻ m : ℤ, ‖w m‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal A * (∫⁻ m : ℤ, ‖w m‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul, show p * (1 / p) = 1 by rw [mul_one_div, div_self hp_ne],
          ENNReal.rpow_one]

end Work.Maximal
