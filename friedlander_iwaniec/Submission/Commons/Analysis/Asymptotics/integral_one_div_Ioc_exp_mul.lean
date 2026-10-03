import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Asymptotics

theorem integral_one_div_Ioc_exp_mul (Y : ℝ) (hY : 0 < Y) :
    ∫ y in Y..Real.exp 1 * Y, 1 / y = 1 := by
  have hb : 0 < Real.exp 1 * Y := by positivity
  rw [integral_one_div_of_pos hY hb]
  rw [mul_div_cancel_right₀ _ (ne_of_gt hY), Real.log_exp]

end Commons.Analysis.Asymptotics