import Mathlib

namespace Work.OffAxis

/-- Crude upper bound for `exp (7/3)`, enough for the far-range arithmetic. -/
private lemma exp_seven_thirds_le : Real.exp (7/3) ≤ 27 := by
  have h3 : Real.exp (3 : ℝ) ≤ 27 := by
    have he : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [he]
    calc Real.exp 1 ^ 3 ≤ (3 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
      _ = 27 := by norm_num
  calc Real.exp (7/3) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
    _ ≤ 27 := h3

theorem tf72_far_arith : ∀ m : ℝ, 200 ≤ |m| →
    (32/35 + Real.exp (7/3) * (3456/343) * (7/3)) / m^2 ≤ 16/315 := by
  intro m hm
  have hm2 : (40000 : ℝ) ≤ m ^ 2 := by
    have h : (200 : ℝ) ^ 2 ≤ |m| ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
    rw [sq_abs] at h
    norm_num at h
    exact h
  have hpos : 0 < m ^ 2 := by linarith
  have hnum : 32/35 + Real.exp (7/3) * (3456/343) * (7/3) ≤ (16/315) * 40000 := by
    nlinarith [exp_seven_thirds_le]
  rw [div_le_iff₀ hpos]
  nlinarith [hnum, hm2]

end Work.OffAxis
