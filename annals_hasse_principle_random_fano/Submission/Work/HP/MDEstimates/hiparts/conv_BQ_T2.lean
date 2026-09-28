import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

namespace Work.HP.MDEstimates.hiparts

theorem conv_BQ_T2 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M)
    (h : 6.96875 * Real.log A + 8 * Real.log M - (2.501 + 1/1000) * Real.log B
        - 3.5 * Real.log Δ ≥ -2000 + 120 * Real.log 2) :
    32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53 * (2 * A / M) ^ (61:ℝ)
      ≤ hiK / 2 * hiTgt A B := by
  have hLHSpos : 0 < 32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2)
      * M ^ 53 * (2 * A / M) ^ (61:ℝ) := by positivity
  have hRHSpos : 0 < hiK / 2 * hiTgt A B := by unfold hiK hiTgt; positivity
  rw [← Real.log_le_log_iff hLHSpos hRHSpos]
  have hLlog : Real.log (32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53
        * (2 * A / M) ^ (61:ℝ))
      = 5 * Real.log 2 + 53 * Real.log 2 + ((9:ℝ)/2 + (1:ℝ)/1000) * Real.log B
        + ((7:ℝ)/2) * Real.log Δ + 53 * Real.log M
        + 61 * (Real.log 2 + Real.log A - Real.log M) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    rw [show (32:ℝ) = (2:ℝ)^5 by norm_num]
    rw [Real.log_pow (2:ℝ) 5, Real.log_pow (2:ℝ) 53, Real.log_pow M 53]
    rw [Real.log_rpow (x := B) hB, Real.log_rpow (x := Δ) hΔ,
        Real.log_rpow (x := 2 * A / M) (by positivity)]
    rw [Real.log_div (show (2 * A) ≠ 0 by positivity) (show M ≠ 0 by positivity),
        Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (show A ≠ 0 by positivity)]
    ring
  have hRlog : Real.log (hiK / 2 * hiTgt A B)
      = 2000 - Real.log 2 + (2175:ℝ)/32 * Real.log A + (1999:ℝ)/1000 * Real.log B := by
    unfold hiK hiTgt
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_rpow (x := A) hA, Real.log_rpow (x := B) hB, Real.log_exp]
    ring
  rw [hLlog, hRlog]
  linarith [h]

end Work.HP.MDEstimates.hiparts
