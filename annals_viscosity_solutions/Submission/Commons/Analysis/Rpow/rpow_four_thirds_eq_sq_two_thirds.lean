import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Rpow

theorem rpow_four_thirds_eq_sq_two_thirds {t : ℝ} (ht : 0 < t) :
    t ^ ((4:ℝ)/3) = (t ^ ((2:ℝ)/3)) ^ 2 := by
  rw [← Real.rpow_mul_natCast (le_of_lt ht) ((2:ℝ)/3) 2]
  norm_num

end Commons.Analysis.Rpow