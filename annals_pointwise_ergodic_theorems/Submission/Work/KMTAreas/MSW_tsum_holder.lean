import Mathlib

open MeasureTheory

namespace Work.KMTAreas

/-- Weighted Hölder inequality for `ℝ≥0∞`-valued series over `ℤ`: for `r > 1`,
`∑ aₘ bₘ ≤ (∑ aₘ ^ r bₘ) ^ (1/r) * (∑ bₘ) ^ (1 - 1/r)`.

This is Hölder's inequality applied to the weight decomposition
`aₘ bₘ = (aₘ ^ r bₘ) ^ (1/r) · bₘ ^ (1 - 1/r)`, with exponents
`p = 1/r` and `q = 1 - 1/r`, whose sum is `1`. -/
theorem MSW_tsum_holder (r : ℝ) (hr : 1 < r) (a b : ℤ → ENNReal) :
    (∑' m : ℤ, a m * b m)
      ≤ (∑' m : ℤ, a m ^ r * b m) ^ (1 / r) * (∑' m : ℤ, b m) ^ (1 - 1 / r) := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have h1r : (0 : ℝ) ≤ 1 / r := by positivity
  have hq0 : (0 : ℝ) ≤ 1 - 1 / r := by
    have : 1 / r < 1 := by
      rw [one_div]
      exact inv_lt_one_of_one_lt₀ hr
    linarith
  have hpq : 1 / r + (1 - 1 / r) = 1 := by ring
  -- the pointwise weight decomposition
  have hpt : ∀ m : ℤ, (a m ^ r * b m) ^ (1 / r) * b m ^ (1 - 1 / r) = a m * b m := by
    intro m
    have h1 : (a m ^ r) ^ (1 / r) = a m := by
      rw [← ENNReal.rpow_mul]
      have : r * (1 / r) = 1 := by
        rw [mul_one_div, div_self hr0.ne']
      rw [this, ENNReal.rpow_one]
    have h2 : b m ^ (1 / r) * b m ^ (1 - 1 / r) = b m := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / r) (1 - 1 / r) h1r hq0]
      rw [hpq, ENNReal.rpow_one]
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1r, h1, mul_assoc, h2]
  have key : (∫⁻ m : ℤ, (a m ^ r * b m) ^ (1 / r) * b m ^ (1 - 1 / r) ∂Measure.count)
      ≤ (∫⁻ m : ℤ, a m ^ r * b m ∂Measure.count) ^ (1 / r)
        * (∫⁻ m : ℤ, b m ∂Measure.count) ^ (1 - 1 / r) :=
    ENNReal.lintegral_mul_norm_pow_le
      (f := fun m : ℤ => a m ^ r * b m) (g := fun m : ℤ => b m)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
      h1r hq0 hpq
  calc (∑' m : ℤ, a m * b m)
      = ∑' m : ℤ, (a m ^ r * b m) ^ (1 / r) * b m ^ (1 - 1 / r) :=
        tsum_congr fun m => (hpt m).symm
    _ = ∫⁻ m : ℤ, (a m ^ r * b m) ^ (1 / r) * b m ^ (1 - 1 / r) ∂Measure.count := by
        rw [← lintegral_count]
    _ ≤ (∫⁻ m : ℤ, a m ^ r * b m ∂Measure.count) ^ (1 / r)
          * (∫⁻ m : ℤ, b m ∂Measure.count) ^ (1 - 1 / r) := key
    _ = (∑' m : ℤ, a m ^ r * b m) ^ (1 / r) * (∑' m : ℤ, b m) ^ (1 - 1 / r) := by
        rw [lintegral_count, lintegral_count]

end Work.KMTAreas
