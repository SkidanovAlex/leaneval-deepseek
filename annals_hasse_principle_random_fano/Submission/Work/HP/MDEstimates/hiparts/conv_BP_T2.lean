import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

namespace Work.HP.MDEstimates.hiparts

/-- `B`-side, `T2` cell of the per-cell arithmetic: the logarithmic hypothesis
dominates the monomial `64 · B^{9/2+1/1000} · Δ^{9/2} · (2A/M)^61`. -/
theorem conv_BP_T2 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M)
    (h : 6.96875 * Real.log A + 61 * Real.log M - (2.501 + 1/1000) * Real.log B
        - 4.5 * Real.log Δ ≥ -2000 + Real.log 128 + 61 * Real.log 2) :
    64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2) * (2 * A / M) ^ (61:ℝ)
      ≤ hiK / 2 * hiTgt A B := by
  have hLpos : (0:ℝ) < 64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2) * (2 * A / M) ^ (61:ℝ) := by
    positivity
  have hRpos : (0:ℝ) < hiK / 2 * hiTgt A B := by
    unfold hiK hiTgt
    positivity
  rw [← Real.log_le_log_iff hLpos hRpos]
  have hLlog : Real.log (64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2) * (2 * A / M) ^ (61:ℝ))
      = Real.log 64 + ((9:ℝ)/2 + (1:ℝ)/1000) * Real.log B + ((9:ℝ)/2) * Real.log Δ
        + 61 * (Real.log 2 + Real.log A - Real.log M) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hB, Real.log_rpow hΔ, Real.log_rpow (by positivity),
        Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)]
  have hRlog : Real.log (hiK / 2 * hiTgt A B)
      = 2000 - Real.log 2 + (2175:ℝ)/32 * Real.log A + (1999:ℝ)/1000 * Real.log B := by
    unfold hiK hiTgt
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) (by norm_num),
        Real.log_exp,
        Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hA, Real.log_rpow hB]
    ring
  rw [hLlog, hRlog]
  have hlog64 : Real.log (64:ℝ) = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have hlog128 : Real.log (128:ℝ) = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]; norm_num
  linarith

end Work.HP.MDEstimates.hiparts
