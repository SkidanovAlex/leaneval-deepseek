import Mathlib

namespace Work.LinnikAreas.DhRepel

theorem integral_sub_self (L : ℝ) : (∫ t in (0:ℝ)..L, (L - t)) = L ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    intervalIntegral.integral_const, integral_id]
  ring

end Work.LinnikAreas.DhRepel
