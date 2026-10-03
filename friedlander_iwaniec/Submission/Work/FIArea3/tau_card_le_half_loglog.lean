import Mathlib
import Submission.Work.FIArea3.JointCount.tau_le_exp_loglog

namespace Work.FIArea3

/-- `log (log 3) ≥ 1/100`.  We show `log 3 ≥ 1.02 = 51/50`, which follows from
`e^{1.02} ≤ 2.7182818286 * (1/0.98) < 3`, and then use `log x ≥ 1 - 1/x`. -/
lemma log_log_three_ge : (1/100 : ℝ) ≤ Real.log (Real.log 3) := by
  have hexp102 : Real.exp (1.02:ℝ) ≤ 3 := by
    have hsplit : Real.exp (1.02:ℝ) = Real.exp 1 * Real.exp (0.02:ℝ) := by
      rw [← Real.exp_add]; norm_num
    have he1 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
    have hlog : (0.02:ℝ) ≤ Real.log (1/(0.98:ℝ)) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 0.98 by norm_num)
      rw [one_div, Real.log_inv]
      linarith
    have he002 : Real.exp (0.02:ℝ) ≤ 1/(0.98:ℝ) := by
      rw [← Real.exp_log (show (0:ℝ) < 1/(0.98:ℝ) by norm_num)]
      exact Real.exp_le_exp.mpr hlog
    have hmul : Real.exp 1 * Real.exp (0.02:ℝ) ≤ 2.7182818286 * (1/(0.98:ℝ)) :=
      mul_le_mul he1 he002 (le_of_lt (Real.exp_pos _)) (by norm_num)
    have hnum : 2.7182818286 * (1/(0.98:ℝ)) ≤ 3 := by norm_num
    rw [hsplit]; linarith
  have hlog3 : (1.02:ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr hexp102
  have hbase : (1:ℝ)/100 ≤ Real.log (1.02:ℝ) := by
    have h1 : 1 - 1/(1.02:ℝ) ≤ Real.log (1.02:ℝ) :=
      JointCount.one_sub_inv_le_log (by norm_num)
    have h2 : (1:ℝ)/100 ≤ 1 - 1/(1.02:ℝ) := by norm_num
    linarith
  have hmono : Real.log (1.02:ℝ) ≤ Real.log (Real.log 3) :=
    Real.log_le_log (by norm_num) hlog3
  linarith

/-- Shift comparison of the Wigert exponent: for `m ≥ 3`,
`(3/2)·log(m+2)/loglog(m+2) ≤ (3/2)·log m/loglog m + 10^4`.

Writing `a = log m`, `b = log(m+2)` and `La = loglog m`, `Lb = loglog(m+2)`, we have
`b = a + log(1 + 2/m) ≤ a + 2/m`, `Lb ≥ La > 0`, whence
`b/Lb - a/La ≤ (2/m)/La`.  Multiplying by `3/2` gives at most `3/(m·La) ≤ 3/(3·(1/100)) = 100 ≤ 10^4`. -/
lemma exp_arg_shift_le (m : ℕ) (hm : 3 ≤ m) :
    (3/2 : ℝ) * Real.log ((m:ℝ)+2) / Real.log (Real.log ((m:ℝ)+2))
      ≤ 3/2 * Real.log (m:ℝ) / Real.log (Real.log (m:ℝ)) + (10:ℝ)^4 := by
  have hmR : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  -- basic positivity / monotonicity
  have hlog3_gt1 : (1:ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have ha1 : (1:ℝ) < Real.log (m:ℝ) :=
    lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hmR)
  have hapos : 0 < Real.log (m:ℝ) := lt_trans one_pos ha1
  have hLapos : 0 < Real.log (Real.log (m:ℝ)) := Real.log_pos ha1
  have hLa_ge : (1/100 : ℝ) ≤ Real.log (Real.log (m:ℝ)) := by
    have h1 : Real.log (Real.log 3) ≤ Real.log (Real.log (m:ℝ)) :=
      Real.log_le_log (Real.log_pos (by norm_num : (1:ℝ) < 3))
        (Real.log_le_log (by norm_num) hmR)
    linarith [log_log_three_ge, h1]
  have hle_ab : Real.log (m:ℝ) ≤ Real.log ((m:ℝ)+2) :=
    Real.log_le_log hmpos (by linarith)
  have hLb_ge : Real.log (Real.log (m:ℝ)) ≤ Real.log (Real.log ((m:ℝ)+2)) :=
    Real.log_le_log hapos hle_ab
  have hLbpos : 0 < Real.log (Real.log ((m:ℝ)+2)) := lt_of_lt_of_le hLapos hLb_ge
  -- `log (m+2) = log m + log ((m+2)/m)`, and the latter is at most `2/m`
  have hb_eq : Real.log ((m:ℝ)+2)
      = Real.log (m:ℝ) + Real.log (((m:ℝ)+2)/(m:ℝ)) := by
    rw [Real.log_div (by linarith : (m:ℝ)+2 ≠ 0) (ne_of_gt hmpos)]
    ring
  have hδ : Real.log (((m:ℝ)+2)/(m:ℝ)) ≤ 2/(m:ℝ) := by
    have hdiv_eq : ((m:ℝ)+2)/(m:ℝ) = 1 + 2/(m:ℝ) := by field_simp
    rw [hdiv_eq]
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2/(m:ℝ) by positivity)
    linarith
  have hb_le : Real.log ((m:ℝ)+2) ≤ Real.log (m:ℝ) + 2/(m:ℝ) := by
    rw [hb_eq]; linarith
  have hnum_nn : (0:ℝ) ≤ Real.log (m:ℝ) + 2/(m:ℝ) := by positivity
  -- main ratio bound
  have hbound : Real.log ((m:ℝ)+2) / Real.log (Real.log ((m:ℝ)+2))
      ≤ Real.log (m:ℝ) / Real.log (Real.log (m:ℝ))
        + (2/(m:ℝ)) / Real.log (Real.log (m:ℝ)) := by
    calc Real.log ((m:ℝ)+2) / Real.log (Real.log ((m:ℝ)+2))
        ≤ (Real.log (m:ℝ) + 2/(m:ℝ)) / Real.log (Real.log ((m:ℝ)+2)) :=
          div_le_div_of_nonneg_right hb_le (le_of_lt hLbpos)
      _ ≤ (Real.log (m:ℝ) + 2/(m:ℝ)) / Real.log (Real.log (m:ℝ)) :=
          div_le_div_of_nonneg_left hnum_nn hLapos hLb_ge
      _ = Real.log (m:ℝ) / Real.log (Real.log (m:ℝ))
            + (2/(m:ℝ)) / Real.log (Real.log (m:ℝ)) := by ring
  -- `3/(m loglog m) ≤ 10^4`
  have hmLa_ge : (3:ℝ)/100 ≤ (m:ℝ) * Real.log (Real.log (m:ℝ)) := by
    have hmul2 := mul_le_mul hmR hLa_ge (by norm_num : (0:ℝ) ≤ 1/100) (le_of_lt hmpos)
    linarith
  have hsmall : (3:ℝ)/((m:ℝ) * Real.log (Real.log (m:ℝ))) ≤ (10:ℝ)^4 := by
    have h100 : (3:ℝ)/((m:ℝ) * Real.log (Real.log (m:ℝ))) ≤ 100 := by
      rw [div_le_iff₀ (mul_pos hmpos hLapos)]
      nlinarith [hmLa_ge]
    norm_num at h100 ⊢
    linarith
  calc (3/2 : ℝ) * Real.log ((m:ℝ)+2) / Real.log (Real.log ((m:ℝ)+2))
      = (3/2 : ℝ) * (Real.log ((m:ℝ)+2) / Real.log (Real.log ((m:ℝ)+2))) := by ring
    _ ≤ (3/2 : ℝ) * (Real.log (m:ℝ) / Real.log (Real.log (m:ℝ))
          + (2/(m:ℝ)) / Real.log (Real.log (m:ℝ))) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (3/2 : ℝ) * Real.log (m:ℝ) / Real.log (Real.log (m:ℝ))
          + 3/((m:ℝ) * Real.log (Real.log (m:ℝ))) := by ring
    _ ≤ (3/2 : ℝ) * Real.log (m:ℝ) / Real.log (Real.log (m:ℝ)) + (10:ℝ)^4 := by
        linarith [hsmall]

theorem tau_card_le_half_loglog (m : ℕ) (hm : 3 ≤ m) :
    (m.divisors.card : ℝ) ≤ Real.exp (3 / 2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) + 10 ^ 4) := by
  have hτ : ((m.divisors.card : ℕ) : ℝ)
      ≤ Real.exp (1.5 * Real.log ((m:ℝ)+2) / Real.log (Real.log ((m:ℝ)+2))) :=
    JointCount.tau_le_exp_loglog m (by omega)
  have h15 : (1.5:ℝ) = 3/2 := by norm_num
  rw [h15] at hτ
  have hshift := exp_arg_shift_le m hm
  exact le_trans hτ (Real.exp_le_exp.mpr hshift)

end Work.FIArea3
