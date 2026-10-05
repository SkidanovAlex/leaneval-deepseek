import Mathlib

namespace Work.RPB1a.Caratheodory.CS

lemma rpow_half_mul_self (a : ENNReal) : a ^ (1/2:ℝ) * a ^ (1/2:ℝ) = a := by
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num),
    show (1/2:ℝ) + 1/2 = 1 by norm_num, ENNReal.rpow_one]

end Work.RPB1a.Caratheodory.CS
