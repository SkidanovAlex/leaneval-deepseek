import Mathlib

namespace Work.FIArea4.Vflip.Vfd

theorem log_pow4_ge (u : ℝ) (hu : (1 : ℝ) / 3 ≤ u) : u + 2 ≤ (u + 1) ^ 4 := by
  have h1 : (0:ℝ) ≤ u - 1/3 := by linarith
  have h2 : (0:ℝ) ≤ (u - 1/3)^2 := by positivity
  have h3 : (0:ℝ) ≤ (u - 1/3)^3 := by positivity
  have h4 : (0:ℝ) ≤ (u - 1/3)^4 := by positivity
  nlinarith [h1, h2, h3, h4]

end Work.FIArea4.Vflip.Vfd
