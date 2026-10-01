import Mathlib

namespace Work.LinnikAreas.Density4

theorem one_sub_exp_neg_le (ε : ℝ) (hε : 0 < ε) : 1 - Real.exp (-ε) ≤ 0.34 * (1 + ε) := by
  -- Numerics for `exp (11/10)`: we need `exp (11/10) ≥ 50/17` and `exp (11/10) ≤ 35/11`.
  have h1 : (50:ℝ)/17 ≤ Real.exp (11/10) := by
    have hge : (11:ℝ)/10 ≤ Real.exp (1/10) := by
      have := Real.add_one_le_exp (1/10); linarith
    have hmul : Real.exp 1 * ((11:ℝ)/10) ≤ Real.exp 1 * Real.exp (1/10) :=
      mul_le_mul_of_nonneg_left hge (Real.exp_pos 1).le
    have heq : Real.exp (11/10) = Real.exp 1 * Real.exp (1/10) := by
      rw [← Real.exp_add]; norm_num
    rw [heq]
    linarith [Real.exp_one_gt_d9, hmul]
  have h2 : Real.exp (11/10) ≤ (35:ℝ)/11 := by
    have hle : Real.exp (1/10) ≤ (10:ℝ)/9 := by
      have h9 : (9:ℝ)/10 ≤ Real.exp (-(1/10)) := by
        have := Real.add_one_le_exp (-(1/10)); linarith
      have hprod : Real.exp (1/10) * Real.exp (-(1/10)) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hm := mul_le_mul_of_nonneg_left h9 (Real.exp_pos (1/10)).le
      rw [hprod] at hm
      nlinarith [hm]
    have hmul : Real.exp 1 * Real.exp (1/10) ≤ Real.exp 1 * ((10:ℝ)/9) :=
      mul_le_mul_of_nonneg_left hle (Real.exp_pos 1).le
    have heq : Real.exp (11/10) = Real.exp 1 * Real.exp (1/10) := by
      rw [← Real.exp_add]; norm_num
    rw [heq]
    linarith [Real.exp_one_lt_d9, hmul]
  -- Key bounds on `c := exp (-(11/10))`.
  have hprod : Real.exp (-(11/10)) * Real.exp (11/10) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hc_le : Real.exp (-(11/10)) ≤ (17:ℝ)/50 := by
    have hm := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(11/10))).le
    rw [hprod] at hm
    nlinarith [hm]
  have hc2 : (33:ℝ)/50 ≤ Real.exp (-(11/10)) * (21/10) := by
    have hstep : (33:ℝ)/50 * Real.exp (11/10) ≤ (21:ℝ)/10 := by
      nlinarith [h2]
    calc (33:ℝ)/50
        = (33:ℝ)/50 * (Real.exp (-(11/10)) * Real.exp (11/10)) := by rw [hprod]; ring
      _ = ((33:ℝ)/50 * Real.exp (11/10)) * Real.exp (-(11/10)) := by ring
      _ ≤ ((21:ℝ)/10) * Real.exp (-(11/10)) :=
            mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-(11/10))).le
      _ = Real.exp (-(11/10)) * (21/10) := by ring
  -- Tangent line of `exp` at `-(11/10)`.
  have ht : Real.exp (-(11/10)) * (21/10 - ε) ≤ Real.exp (-ε) := by
    have h := Real.add_one_le_exp (11/10 - ε)
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(11/10))).le
    have heq : Real.exp (-(11/10)) * Real.exp (11/10 - ε) = Real.exp (-ε) := by
      rw [← Real.exp_add]; ring_nf
    rw [heq] at hmul
    have heq2 : Real.exp (-(11/10)) * ((11/10 - ε) + 1) = Real.exp (-(11/10)) * (21/10 - ε) := by
      ring
    rw [heq2] at hmul
    exact hmul
  have hkey : (33:ℝ)/50 - (17:ℝ)/50 * ε ≤ Real.exp (-ε) := by
    have hcε : Real.exp (-(11/10)) * ε ≤ (17:ℝ)/50 * ε :=
      mul_le_mul_of_nonneg_right hc_le hε.le
    have hexpand : Real.exp (-(11/10)) * (21/10 - ε)
        = Real.exp (-(11/10)) * (21/10) - Real.exp (-(11/10)) * ε := by ring
    rw [hexpand] at ht
    linarith [ht, hc2, hcε]
  linarith [hkey]

end Work.LinnikAreas.Density4
