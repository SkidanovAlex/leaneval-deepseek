import Mathlib

namespace Commons.Analysis.Arithmetic

theorem indicial_four_ne_zero (N : ℤ) (hN : N ≤ 1) :
    (-(45 / 2) : ℚ) + 21 * (N : ℚ) + (-(39 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
      + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) ≠ 0 := by
  have hx : (N : ℚ) ≤ 1 := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (2 - (N : ℚ)) * (3 - (N : ℚ)) * (3 - 2 * (N : ℚ)) * (5 - 2 * (N : ℚ)) := by
    have h1 : (0 : ℚ) < 2 - (N : ℚ) := by linarith
    have h2 : (0 : ℚ) < 3 - (N : ℚ) := by linarith
    have h3 : (0 : ℚ) < 3 - 2 * (N : ℚ) := by linarith
    have h4 : (0 : ℚ) < 5 - 2 * (N : ℚ) := by linarith
    exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4
  have hid : (-(45 / 2) : ℚ) + 21 * (N : ℚ) + (-(39 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
      + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3))
      = -(1 / 4) * ((2 - (N : ℚ)) * (3 - (N : ℚ)) * (3 - 2 * (N : ℚ)) * (5 - 2 * (N : ℚ))) := by
    ring
  have hneg : (-(45 / 2) : ℚ) + 21 * (N : ℚ) + (-(39 / 4)) * ((N : ℚ) * ((N : ℚ) - 1))
      + 3 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
      + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) < 0 := by
    rw [hid]
    nlinarith [hpos]
  exact ne_of_lt hneg

end Commons.Analysis.Arithmetic
