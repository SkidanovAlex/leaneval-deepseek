import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

namespace Work.HP.MDEstimates.hiparts

/-- Logarithm of the left-hand side of `conv_AQ_T2`, expanded into logarithms of the
individual variables. -/
private lemma log_lhs_AQ_T2 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ)
    (hM : 0 < M) (k : ℕ) :
    Real.log (32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53 * (2 * A / M) ^ ((67:ℝ) - (k:ℝ)))
    = (125 - (k:ℝ)) * Real.log 2 + (67 - (k:ℝ)) * Real.log A - (14 - (k:ℝ)) * Real.log M
      + (6 + (1:ℝ)/1000) * Real.log B + 2 * Real.log Δ := by
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]
  rw [Real.log_pow]
  rw [Real.log_rpow hB]
  rw [Real.log_pow]
  rw [Real.log_pow]
  rw [Real.log_rpow (by positivity : (0:ℝ) < 2 * A / M)]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

/-- Logarithm of the right-hand side of `conv_AQ_T2`, expanded into logarithms of
the individual variables. -/
private lemma log_rhs_AQ_T2 (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.log (hiK / 2 * hiTgt A B)
    = 2000 - Real.log 2 + (2175/32) * Real.log A + (1999/1000) * Real.log B := by
  unfold hiK hiTgt
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_div (by positivity) (by norm_num)]
  rw [Real.log_exp]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow hA]
  rw [Real.log_rpow hB]
  ring

theorem conv_AQ_T2 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M) (k : ℕ)
    (hk : 4 ≤ k) (hk67 : k ≤ 67)
    (h : ((k:ℝ) + 31/32) * Real.log A + (14 - (k:ℝ)) * Real.log M
        - (4.001 + 1/1000) * Real.log B - 2 * Real.log Δ
        ≥ -2000 + ((126:ℝ) - (k:ℝ)) * Real.log 2) :
    32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53 * (2 * A / M) ^ ((67:ℝ) - (k:ℝ))
      ≤ hiK / 2 * hiTgt A B := by
  have hLpos : 0 < 32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53
      * (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) := by positivity
  have hRpos : 0 < hiK / 2 * hiTgt A B := by
    have h1 : 0 < hiK := hiK_pos
    have h2 : 0 < hiTgt A B := hiTgt_pos hA hB
    positivity
  apply (Real.log_le_log_iff hLpos hRpos).mp
  rw [log_lhs_AQ_T2 A B Δ M hA hB hΔ hM k, log_rhs_AQ_T2 A B hA hB]
  linarith [h]

end Work.HP.MDEstimates.hiparts
