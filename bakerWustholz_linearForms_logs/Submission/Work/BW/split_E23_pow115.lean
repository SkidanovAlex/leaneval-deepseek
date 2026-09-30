import Mathlib
import Submission.Work.BW.split_E23_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `pI r d = ⌊50 log(2rd)⌋₊` dominates `6 log(2rd)` from the base-`1.15`
logarithm: since `log 1.15 ≥ 3/23` and `2rd ≥ 4`, we have
`50 log 1.15 - 6 ≥ 12/23 > 0` and `log(2rd) ≥ 1`, so
`(50 log(2rd) - 1) log 1.15 ≥ 6 log(2rd)`; flooring costs at most `1`. -/
theorem split_E23_pow115 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (2*(r:ℝ)*d)^6 ≤ (1.15:ℝ)^(pI r d) := by
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hX4 : (4:ℝ) ≤ 2*(r:ℝ)*d := by nlinarith
  have hXpos : (0:ℝ) < 2*(r:ℝ)*d := by linarith
  have hlog4 : (1:ℝ) ≤ Real.log 4 := by
    have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      have : (4:ℝ) = 2^2 := by norm_num
      rw [this, Real.log_pow]; norm_num
    rw [h4]
    have := Real.log_two_gt_d9
    linarith
  have hL : (1:ℝ) ≤ Real.log (2*(r:ℝ)*d) := by
    have := Real.log_le_log (show (0:ℝ) < 4 by norm_num) hX4
    linarith
  have hc_lo : (3/23 : ℝ) ≤ Real.log 1.15 := by
    have h115 : (1.15:ℝ) = 23/20 := by norm_num
    have hinv : Real.log ((20:ℝ)/23) = -Real.log ((23:ℝ)/20) := by
      rw [show (20:ℝ)/23 = ((23:ℝ)/20)⁻¹ by norm_num, Real.log_inv]
    have hle := Real.log_le_sub_one_of_pos (show (0:ℝ) < (20:ℝ)/23 by norm_num)
    rw [hinv] at hle
    rw [h115]
    linarith
  have hc_hi : Real.log 1.15 ≤ 0.15 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1.15 by norm_num)
    linarith
  have hc_pos : (0:ℝ) < Real.log 1.15 := by linarith [hc_lo]
  have hcoef : (0:ℝ) < 50 * Real.log 1.15 - 6 := by linarith [hc_lo]
  have h1 : (12/23 : ℝ) ≤ Real.log (2*(r:ℝ)*d) * (50 * Real.log 1.15 - 6) := by
    have := mul_le_mul_of_nonneg_right hL (le_of_lt hcoef)
    linarith [hc_lo]
  have h2 : Real.log 1.15 ≤ (12/23 : ℝ) := by linarith [hc_hi]
  have hcore : 6 * Real.log (2*(r:ℝ)*d) ≤
      (50 * Real.log (2*(r:ℝ)*d) - 1) * Real.log 1.15 := by
    nlinarith [h1, h2]
  have hn_lt : 50 * Real.log (2*(r:ℝ)*d) - 1 < (pI r d : ℝ) := by
    have h := Nat.lt_floor_add_one (50 * Real.log (2*(r:ℝ)*d))
    have heq : ((⌊50 * Real.log (2*(r:ℝ)*d)⌋₊ : ℕ) : ℝ) = (pI r d : ℝ) := by
      rw [← pI]
    rw [heq] at h; linarith
  have hmain : 6 * Real.log (2*(r:ℝ)*d) ≤ (pI r d : ℝ) * Real.log 1.15 := by
    have := mul_lt_mul_of_pos_right hn_lt hc_pos
    linarith
  have hX6 : (2*(r:ℝ)*d)^6 = Real.exp (6 * Real.log (2*(r:ℝ)*d)) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < (2*(r:ℝ)*d)^6)]
    congr 1
    rw [Real.log_pow]; norm_num
  have h115n : (1.15:ℝ)^(pI r d) = Real.exp ((pI r d : ℝ) * Real.log 1.15) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < (1.15:ℝ)^(pI r d))]
    congr 1
    rw [Real.log_pow]
  rw [hX6, h115n]
  exact Real.exp_le_exp.mpr hmain

end Work.BW
