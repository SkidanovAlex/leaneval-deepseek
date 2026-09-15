import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory

namespace Commons.MeasureTheory.Integral

theorem integral_Ioi_inv_sq {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Set.Ioi δ, (t ^ 2)⁻¹) = δ⁻¹ := by
  have hrpow : ∀ t ∈ Set.Ioi δ, (t ^ 2)⁻¹ = t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_trans hδ ht)
    rw [← Real.rpow_natCast t 2, ← Real.rpow_neg ht0]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hrpow,
    integral_Ioi_rpow_of_lt (show (-2:ℝ) < -1 by norm_num) hδ]
  rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

end Commons.MeasureTheory.Integral