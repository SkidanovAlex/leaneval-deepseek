import Mathlib.Analysis.Normed.Group.Real

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

theorem one_le_int_norm_cast (c : ℤ) (h : c ≠ 0) : (1 : ℝ) ≤ ‖(c : ℝ)‖ := by
  rw [Real.norm_eq_abs]
  exact_mod_cast (Int.one_le_abs h : (1 : ℤ) ≤ |c|)

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree