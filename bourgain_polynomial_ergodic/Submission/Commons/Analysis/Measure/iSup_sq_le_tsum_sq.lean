import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Measure

open scoped BigOperators ENNReal

/-- A supremum is controlled by the `ℓ²`-norm of the family: for a countable family
`u : ι → ℝ≥0∞`, `(⨆ i, u i) ^ 2 ≤ ∑'_i (u i) ^ 2`. -/
theorem iSup_sq_le_tsum_sq {ι : Type*} [Countable ι] (u : ι → ℝ≥0∞) :
    (⨆ i, u i) ^ (2 : ℝ) ≤ ∑' i, (u i) ^ (2 : ℝ) := by
  set T := ∑' i, (u i) ^ (2 : ℝ) with hT
  have hterm : ∀ i, (u i) ^ (2 : ℝ) ≤ T := fun i => by
    rw [hT]; exact ENNReal.le_tsum (f := fun i => (u i) ^ (2 : ℝ)) i
  have hle : ∀ i, u i ≤ T ^ ((2 : ℝ)⁻¹) := fun i =>
    (ENNReal.le_rpow_inv_iff (show (0 : ℝ) < 2 by norm_num)).mpr (hterm i)
  have hsup : (⨆ i, u i) ≤ T ^ ((2 : ℝ)⁻¹) := iSup_le hle
  calc (⨆ i, u i) ^ (2 : ℝ)
      ≤ (T ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hsup (by norm_num)
    _ = T := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one]

end Commons.Analysis.Measure