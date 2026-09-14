import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

/-- For `D > 0`, `c > 0` with `8 / c ^ 2 ≤ D` we have `log (2 * D) ≤ c * D`. -/
theorem log_two_mul_le_mul_of_ge {D c : ℝ} (hD : 0 < D) (hc : 0 < c)
    (h : 8 / c ^ 2 ≤ D) : Real.log (2 * D) ≤ c * D := by
  have hc2 : (0 : ℝ) < c ^ 2 := pow_pos hc 2
  -- `8 ≤ c ^ 2 * D`
  have h8 : 8 ≤ c ^ 2 * D := by
    have := (div_le_iff₀ hc2).mp h
    linarith [this]
  set u := c * D with hu
  have hu_pos : 0 < u := mul_pos hc hD
  -- `8 ≤ c * u`
  have hcu : 8 ≤ c * u := by
    have hcd : c * (c * D) = c ^ 2 * D := by ring
    have : c * u = c ^ 2 * D := by rw [hu, hcd]
    rw [this]; exact h8
  -- hence `8 / u ≤ c`
  have hc_ge : 8 / u ≤ c := by
    rw [div_le_iff₀ hu_pos]; linarith [hcu]
  -- hence `8 * D ≤ u ^ 2`, i.e. `2 * D ≤ u ^ 2 / 4`
  have h8D : 8 * D ≤ u ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hc_ge (le_of_lt hD)
    have hrew : (8 / u) * D = 8 * D / u := by ring
    rw [hrew, ← hu] at hmul
    rw [div_le_iff₀ hu_pos] at hmul
    linarith [hmul]
  have h2D : 2 * D ≤ u ^ 2 / 4 := by linarith [h8D]
  calc Real.log (2 * D) ≤ Real.log (u ^ 2 / 4) :=
        Real.log_le_log (by linarith) h2D
    _ = 2 * Real.log (u / 2) := by
        have : u ^ 2 / 4 = (u / 2) ^ 2 := by ring
        rw [this, Real.log_pow]; ring
    _ ≤ u := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < u / 2)
        linarith
    _ = c * D := hu

end Commons.Analysis.Real