import Mathlib

namespace Work.KMTAreas.A7

/-- For a positive exponent `q`, the map `x ↦ x ^ q` on `ℝ≥0∞` preserves arbitrary
suprema: it is monotone and left-invertible by `x ↦ x ^ (1/q)`. -/
theorem rpow_iSup_ennreal {ι : Type*} (b : ι → ENNReal) {q : ℝ} (hq : 0 < q) :
    (⨆ i, b i) ^ q = ⨆ i, (b i) ^ q := by
  refine le_antisymm ?_ ?_
  · -- `(⨆ b)^q ≤ ⨆ b^q`, using that `x ↦ x^(1/q)` is a left inverse of `x ↦ x^q`.
    refine (ENNReal.rpow_le_rpow_iff (one_div_pos.mpr hq)).mp ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq), ENNReal.rpow_one]
    refine iSup_le fun i => ?_
    have hbi : b i = ((b i) ^ q) ^ (1 / q) := by
      rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq), ENNReal.rpow_one]
    rw [hbi]
    exact ENNReal.rpow_le_rpow (le_iSup (fun j => (b j) ^ q) i) (one_div_nonneg.mpr hq.le)
  · -- `⨆ b^q ≤ (⨆ b)^q` by monotonicity.
    exact iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup b i) hq.le

end Work.KMTAreas.A7
