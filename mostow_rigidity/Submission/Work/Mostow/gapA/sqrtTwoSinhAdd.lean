import Mathlib

namespace Work.Mostow.gapA

/-- Auxiliary numerical bound: `exp 1 ≥ 8/3`, from the Taylor partial sum of `exp` at `1`. -/
lemma exp_one_ge_eight_thirds : (8 / 3 : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
  norm_num at h
  linarith

/-- Auxiliary numerical bound: `exp (-1) ≤ 1/2`. -/
lemma exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have h3 : 1 / Real.exp 1 ≤ 1 / (2 : ℝ) := one_div_le_one_div_of_le (by norm_num) h2
  rw [Real.exp_neg]
  simpa using h3

/-- Auxiliary numerical bound: `sinh 1 ≥ 1.05`. -/
lemma one_point_zero_five_le_sinh_one : (1.05 : ℝ) ≤ Real.sinh 1 := by
  rw [Real.sinh_eq]
  linarith [exp_one_ge_eight_thirds, exp_neg_one_le_half]

/-- Auxiliary numerical bound: `cosh 1 ≥ √2`. -/
lemma sqrt_two_le_cosh_one : Real.sqrt 2 ≤ Real.cosh 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sinh_sq 1, one_point_zero_five_le_sinh_one]

theorem sqrtTwoSinhAdd (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt 2 * Real.sinh ρ + 1.05 ≤ Real.sinh (ρ + 1) := by
  have hsinhρ : 0 ≤ Real.sinh ρ := by
    rw [← Real.sinh_zero]
    exact Real.sinh_le_sinh.mpr hρ
  rw [Real.sinh_add, mul_comm (Real.sinh ρ) (Real.cosh 1)]
  have h1 : Real.sqrt 2 * Real.sinh ρ ≤ Real.cosh 1 * Real.sinh ρ :=
    mul_le_mul_of_nonneg_right sqrt_two_le_cosh_one hsinhρ
  have h2 : (1.05 : ℝ) ≤ Real.cosh ρ * Real.sinh 1 := by
    have := mul_le_mul (Real.one_le_cosh ρ) one_point_zero_five_le_sinh_one
      (by norm_num) (by positivity)
    simpa using this
  linarith

end Work.Mostow.gapA
