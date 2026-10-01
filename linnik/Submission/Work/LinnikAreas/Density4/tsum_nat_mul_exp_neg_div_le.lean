import Mathlib

namespace Work.LinnikAreas.Density4

/-- For `X ≥ 1`, `∑ₙ n · e^{-n/X} ≤ (X+1)^2`.  Since `∑ₙ n r^n = r/(1-r)^2`,
it suffices that `1 - e^{-1/X} ≥ 1/(X+1)`, which follows from `1 + 1/X ≤ e^{1/X}`. -/
theorem tsum_nat_mul_exp_neg_div_le (X : ℝ) (hX : 1 ≤ X) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / X)) ^ n) ≤ (X + 1) ^ 2 := by
  have hXpos : 0 < X := by linarith
  have hX1pos : 0 < X + 1 := by linarith
  set r : ℝ := Real.exp (-(1 / X)) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt_one : r < 1 := by
    rw [hr_def, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / X := by positivity
    linarith
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (le_of_lt hr_pos)]
    exact hr_lt_one
  have htsum := tsum_coe_mul_geometric_of_norm_lt_one (r := r) hnorm
  rw [htsum]
  have hden : 1 / (X + 1) ≤ 1 - r := by
    have h1 : 1 / X + 1 ≤ Real.exp (1 / X) := Real.add_one_le_exp (1 / X)
    have hexpinv : r ≤ (1 / X + 1)⁻¹ := by
      rw [hr_def, Real.exp_neg]
      exact inv_anti₀ (by positivity) h1
    have hXexpr : (1 / X + 1)⁻¹ = X / (X + 1) := by
      rw [show 1 / X + 1 = (X + 1) / X by field_simp; ring, inv_div]
    rw [hXexpr] at hexpinv
    have h2 : 1 - X / (X + 1) = 1 / (X + 1) := by field_simp; ring
    linarith
  have hdenpos : 0 < 1 - r := by
    have : (0 : ℝ) < 1 / (X + 1) := by positivity
    linarith
  have hmain : 1 / (1 - r) ^ 2 ≤ (X + 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 - r) ^ 2)]
    have h1 : 1 ≤ (X + 1) * (1 - r) := by
      have hh := mul_le_mul_of_nonneg_left hden (le_of_lt hX1pos)
      have hone : (X + 1) * (1 / (X + 1)) = 1 := by field_simp
      linarith
    have hsq : (1 : ℝ) ≤ ((X + 1) * (1 - r)) ^ 2 := by
      nlinarith [h1, sq_nonneg ((X + 1) * (1 - r) - 1)]
    have h3 : ((X + 1) * (1 - r)) ^ 2 = (X + 1) ^ 2 * (1 - r) ^ 2 := by ring
    linarith
  calc r / (1 - r) ^ 2 ≤ 1 / (1 - r) ^ 2 :=
        div_le_div_of_nonneg_right (le_of_lt hr_lt_one) (by positivity)
    _ ≤ (X + 1) ^ 2 := hmain

end Work.LinnikAreas.Density4
