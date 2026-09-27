import Mathlib

namespace Work.EKLComp

/-- Upper bound for `Real.exp 3`, used to control the size of the shearing term. -/
theorem exp_three_lt_twentyseven : Real.exp 3 < 27 := by
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  calc Real.exp 1 ^ 3 < 3 ^ 3 := by
        apply pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1))
        norm_num
    _ = 27 := by norm_num

theorem shear_estimate (δ ε : ℝ) (hε : 0 < ε) (hεδ : 2600 * ε ≤ δ)
    {c b a : ℝ} (hc : |c| ≤ Real.exp 3 * ε) (hb : |b| < ε) (ha : |a| ≤ 2) :
    |b - c * a| < δ := by
  have hexp3 : Real.exp 3 < 27 := exp_three_lt_twentyseven
  -- triangle inequality
  have htri : |b - c * a| ≤ |b| + |c * a| := by
    calc |b - c * a| = |b + -(c * a)| := by rw [sub_eq_add_neg]
      _ ≤ |b| + |-(c * a)| := abs_add_le _ _
      _ = |b| + |c * a| := by rw [abs_neg]
  -- bound the shearing term `|c * a|`
  have hca : |c * a| ≤ (Real.exp 3 * ε) * 2 := by
    rw [abs_mul]
    exact mul_le_mul hc ha (abs_nonneg a)
      (mul_nonneg (le_of_lt (Real.exp_pos 3)) (le_of_lt hε))
  -- the whole sum is far below `2600 * ε`
  have hsum : |b| + |c * a| < 2600 * ε := by
    have h2 : |b| + |c * a| < ε + (Real.exp 3 * ε) * 2 :=
      add_lt_add_of_lt_of_le hb hca
    have h3 : ε + (Real.exp 3 * ε) * 2 < 2600 * ε := by nlinarith [hexp3, hε]
    linarith
  exact lt_of_le_of_lt htri (lt_of_lt_of_le hsum hεδ)

end Work.EKLComp
