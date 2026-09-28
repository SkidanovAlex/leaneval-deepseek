import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

set_option linter.unusedVariables false

namespace Work.HP.MDEstimates.hiparts

/-- Per-cell arithmetic estimate (`A`,`P` case, exponent `k`): if the weighted log-combination
bound `h` holds then the monomial `64 B^{6+1/1000} Δ³ (2A/M)^{67-k}` is dominated by
`K/2 · A^{68-1/32} B^{2-1/1000}`.  Proved by taking logarithms of both sides. -/
theorem conv_AP_T2 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M) (k : ℕ)
    (hk : 4 ≤ k) (hk67 : k ≤ 67)
    (h : ((k:ℝ) + 31/32) * Real.log A + ((67:ℝ) - (k:ℝ)) * Real.log M
        - (4.001 + 1/1000) * Real.log B - 3 * Real.log Δ
        ≥ -2000 + Real.log 128 + ((67:ℝ) - (k:ℝ)) * Real.log 2) :
    64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3 * (2 * A / M) ^ ((67:ℝ) - (k:ℝ))
      ≤ hiK / 2 * hiTgt A B := by
  have hLpos : 0 < 64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3 * (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) := by
    have h1 : 0 < B ^ (6 + (1:ℝ)/1000) := Real.rpow_pos_of_pos hB _
    have h2 : 0 < Δ ^ 3 := by positivity
    have h3 : 0 < (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hRpos : 0 < hiK / 2 * hiTgt A B := by
    have := hiTgt_pos hA hB
    have hkpos := hiK_pos
    positivity
  apply (Real.log_le_log_iff hLpos hRpos).mp
  have hlogL : Real.log (64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3 * (2 * A / M) ^ ((67:ℝ) - (k:ℝ)))
      = Real.log 64 + (6 + (1:ℝ)/1000) * Real.log B + 3 * Real.log Δ
        + ((67:ℝ) - (k:ℝ)) * (Real.log 2 + Real.log A - Real.log M) := by
    rw [Real.log_mul, Real.log_mul, Real.log_mul, Real.log_rpow, Real.log_pow, Real.log_rpow,
      Real.log_div, Real.log_mul]
    · ring
    all_goals positivity
  have hlogR : Real.log (hiK / 2 * hiTgt A B)
      = 2000 - Real.log 2 + (2175:ℝ)/32 * Real.log A + (1999:ℝ)/1000 * Real.log B := by
    have hKne : hiK ≠ 0 := hiK_pos.ne'
    have hTne : hiTgt A B ≠ 0 := (hiTgt_pos hA hB).ne'
    have hTdef : hiTgt A B = A ^ ((2175:ℝ)/32) * B ^ ((1999:ℝ)/1000) := rfl
    rw [Real.log_mul (x := hiK/2) (y := hiTgt A B) (by positivity) hTne,
        Real.log_div (x := hiK) (y := 2) hKne (by norm_num),
        show Real.log hiK = 2000 from by
          rw [show hiK = Real.exp 2000 from rfl]; exact Real.log_exp 2000,
        hTdef,
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hA, Real.log_rpow hB]
    ring
  have hl64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
    norm_num
  have hl128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]
    norm_num
  have h2175 : (2175:ℝ)/32 = (k:ℝ) + 31/32 + ((67:ℝ) - (k:ℝ)) := by ring
  rw [hlogL, hlogR, h2175]
  linarith [h, hl64, hl128]

end Work.HP.MDEstimates.hiparts
