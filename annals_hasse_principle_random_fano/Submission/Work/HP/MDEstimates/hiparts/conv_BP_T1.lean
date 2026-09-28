import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

namespace Work.HP.MDEstimates.hiparts

theorem conv_BP_T1 (A B Δ : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ)
    (h : -5.96875 * Real.log A + (6.501 + 1/1000) * Real.log B - 1.5 * Real.log Δ
        ≤ 2000 - Real.log 128) :
    64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2)
        * (A ^ (62:ℝ) * B ^ (4:ℝ) * Δ ^ (-6:ℝ))
      ≤ hiK / 2 * hiTgt A B := by
  have hLpos : 0 < 64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2)
        * (A ^ (62:ℝ) * B ^ (4:ℝ) * Δ ^ (-6:ℝ)) := by positivity
  have hRpos : 0 < hiK / 2 * hiTgt A B := by unfold hiK hiTgt; positivity
  rw [← Real.log_le_log_iff hLpos hRpos]
  have hlogL : Real.log (64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2)
        * (A ^ (62:ℝ) * B ^ (4:ℝ) * Δ ^ (-6:ℝ)))
      = Real.log 64 + ((9:ℝ)/2 + 1/1000) * Real.log B + (9:ℝ)/2 * Real.log Δ
        + (62 * Real.log A + 4 * Real.log B + (-6) * Real.log Δ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity),
        Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  have hlogR : Real.log (hiK / 2 * hiTgt A B)
      = 2000 - Real.log 2 + (2175/32) * Real.log A + (1999/1000) * Real.log B := by
    unfold hiK hiTgt
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num),
        Real.log_exp]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
        Real.log_rpow (by positivity)]
    ring
  rw [hlogL, hlogR]
  have hlog128 : Real.log 128 = Real.log 64 + Real.log 2 := by
    rw [show (128:ℝ) = 64 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  nlinarith [h, hlog128]

end Work.HP.MDEstimates.hiparts
