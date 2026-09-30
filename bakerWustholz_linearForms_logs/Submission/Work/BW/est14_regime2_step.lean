import Mathlib
import Submission.Work.BW.log_div_le_two_div_sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem est14_regime2_step (n : ℕ) (hn : 3263443 ≤ n) :
    ((Real.log ((n : ℝ) + 1)) ^ 2 - (Real.log (n : ℝ)) ^ 2) / Real.log 2
      + 2 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
      + (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) ≤ 0.016 := by
  have hnR : (3263443 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hL0nn : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  -- Difference bounds.
  have hd1 : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have hx : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ) + 1)) (ne_of_gt hnpos)] at h
    have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp
      ring
    linarith [h, heq]
  have hd2 : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ 1 / (n : ℝ) := by
    have hx : (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ) + 2))
      (ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ) + 1))] at h
    have heq : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
      one_div_le_one_div_of_le hnpos (by linarith)
    linarith [h, heq, hle]
  -- Bound on the first term.
  have hterm1 : ((Real.log ((n : ℝ) + 1)) ^ 2 - (Real.log (n : ℝ)) ^ 2) / Real.log 2
      ≤ 8 / Real.sqrt (n : ℝ) + 2 / (n : ℝ) := by
    have hBnn : 0 ≤ Real.log ((n : ℝ) + 1) + Real.log (n : ℝ) := by
      have h1 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      linarith
    have hBbound : Real.log ((n : ℝ) + 1) + Real.log (n : ℝ)
        ≤ 2 * Real.log (n : ℝ) + 1 / (n : ℝ) := by linarith [hd1]
    have hipos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have hs1 : (Real.log ((n : ℝ) + 1) + Real.log (n : ℝ))
          * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ (Real.log ((n : ℝ) + 1) + Real.log (n : ℝ)) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hd1 hBnn
    have hs2 : (Real.log ((n : ℝ) + 1) + Real.log (n : ℝ)) * (1 / (n : ℝ))
        ≤ (2 * Real.log (n : ℝ) + 1 / (n : ℝ)) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hBbound hipos
    have hnum : (Real.log ((n : ℝ) + 1) + Real.log (n : ℝ))
          * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ (2 * Real.log (n : ℝ) + 1 / (n : ℝ)) * (1 / (n : ℝ)) := le_trans hs1 hs2
    have hu : Real.log (n : ℝ) / (n : ℝ) ≤ 2 / Real.sqrt (n : ℝ) :=
      log_div_le_two_div_sqrt hn1
    have hYnn : (0 : ℝ) ≤ 2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
      have h3 : (0 : ℝ) ≤ (2 * Real.log (n : ℝ)) / (n : ℝ) :=
        div_nonneg (by linarith) (le_of_lt hnpos)
      have h4 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
      linarith
    have hYdiv : (2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2) / Real.log 2
        ≤ 2 * (2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2) := by
      rw [div_le_iff₀ hlog2pos]
      have hprod : (0 : ℝ) ≤ (2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2)
          * (2 * Real.log 2 - 1) := mul_nonneg hYnn (by linarith [hlog2half])
      nlinarith [hprod]
    have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hn1]
    have hsq : 1 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnpos hnle
    have hB2 : 2 / (n : ℝ) ^ 2 ≤ 2 / (n : ℝ) := by
      simp only [div_eq_mul_inv] at hsq ⊢
      linarith
    have hA : 4 * (Real.log (n : ℝ) / (n : ℝ)) ≤ 8 / Real.sqrt (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 by norm_num)
      calc 4 * (Real.log (n : ℝ) / (n : ℝ)) ≤ 4 * (2 / Real.sqrt (n : ℝ)) := h
        _ = 8 / Real.sqrt (n : ℝ) := by ring
    have hfinal2 : 2 * (2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2)
        ≤ 8 / Real.sqrt (n : ℝ) + 2 / (n : ℝ) := by
      simp only [div_eq_mul_inv] at hA hB2 ⊢
      nlinarith [hA, hB2]
    calc ((Real.log ((n : ℝ) + 1)) ^ 2 - (Real.log (n : ℝ)) ^ 2) / Real.log 2
        = ((Real.log ((n : ℝ) + 1) + Real.log (n : ℝ))
            * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))) / Real.log 2 := by
          rw [sq_sub_sq]
      _ ≤ ((2 * Real.log (n : ℝ) + 1 / (n : ℝ)) * (1 / (n : ℝ))) / Real.log 2 :=
          div_le_div_of_nonneg_right hnum (le_of_lt hlog2pos)
      _ = (2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2) / Real.log 2 := by ring
      _ ≤ 2 * (2 * Real.log (n : ℝ) / (n : ℝ) + 1 / (n : ℝ) ^ 2) := hYdiv
      _ ≤ 8 / Real.sqrt (n : ℝ) + 2 / (n : ℝ) := hfinal2
  have hterm2 : 2 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 2 / (n : ℝ) := by
    simp only [div_eq_mul_inv] at hd1 ⊢
    linarith
  have htotal : ((Real.log ((n : ℝ) + 1)) ^ 2 - (Real.log (n : ℝ)) ^ 2) / Real.log 2
      + 2 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
      + (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1))
      ≤ 8 / Real.sqrt (n : ℝ) + 5 / (n : ℝ) := by
    simp only [div_eq_mul_inv] at hterm1 hterm2 hd2 ⊢
    linarith
  have hsqrt : (1806 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt' (show (0 : ℝ) < 1806 by norm_num)]
    nlinarith [hnR]
  have hfin : 8 / Real.sqrt (n : ℝ) + 5 / (n : ℝ) ≤ 0.016 := by
    have h1 : 8 / Real.sqrt (n : ℝ) ≤ 8 / 1806 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrt
    have h2 : 5 / (n : ℝ) ≤ 5 / 3263443 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    have h3 : (8 : ℝ) / 1806 + 5 / 3263443 ≤ 0.016 := by norm_num
    linarith [h1, h2, h3]
  linarith [htotal, hfin]

end Work.BW
