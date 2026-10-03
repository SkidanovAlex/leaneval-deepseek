import Mathlib

/-!
# An integral bound for a shifted reciprocal

For `0 ≤ Y ≤ y` and `1 ≤ a + Y` one has

  `∫ t in Y..y, (a + t)⁻¹ ≤ Real.log (2 + y)`.

Indeed, since `a + t ≥ a + Y ≥ 1 > 0` on `[Y, y]` the substitution `u = a + t` gives

  `∫ t in Y..y, (a + t)⁻¹ = ∫ u in a + Y..a + y, u⁻¹ = Real.log ((a + y) / (a + Y))`,

and `(a + y) / (a + Y) = 1 + (y - Y) / (a + Y) ≤ 1 + (y - Y) ≤ 2 + y` because
`a + Y ≥ 1` and `Y ≥ 0`.  Monotonicity of the logarithm finishes the job.
-/

namespace Work.Pert

theorem integral_inv_shift_le_log {a Y y : ℝ} (hY : 0 ≤ Y) (hYy : Y ≤ y) (ha : 1 ≤ a + Y) :
    ∫ t in Y..y, (a + t)⁻¹ ≤ Real.log (2 + y) := by
  have hYpos : 0 < a + Y := by linarith
  have hypos : 0 < a + y := by linarith
  have hkey : (∫ t in Y..y, (a + t)⁻¹) = Real.log ((a + y) / (a + Y)) := by
    have h1 : (∫ t in Y..y, (a + t)⁻¹) = ∫ x in a + Y..a + y, x⁻¹ := by
      have h := intervalIntegral.integral_comp_add_mul (f := fun u : ℝ => u⁻¹)
        (a := Y) (b := y) (c := (1 : ℝ)) (d := a) one_ne_zero
      simp only [one_mul, inv_one, one_smul] at h
      exact h
    rw [h1, integral_inv_of_pos hYpos hypos]
  rw [hkey]
  apply Real.log_le_log (div_pos hypos hYpos)
  have hd : 0 ≤ y - Y := by linarith
  have hsplit : (a + y) / (a + Y) = 1 + (y - Y) / (a + Y) := by
    have hh : a + y = (a + Y) + (y - Y) := by ring
    rw [hh, add_div, div_self (ne_of_gt hYpos)]
  rw [hsplit]
  have hle : (y - Y) / (a + Y) ≤ y - Y := by
    have h := div_le_div_of_nonneg_left hd (show (0 : ℝ) < 1 by norm_num) ha
    simpa using h
  linarith

end Work.Pert
