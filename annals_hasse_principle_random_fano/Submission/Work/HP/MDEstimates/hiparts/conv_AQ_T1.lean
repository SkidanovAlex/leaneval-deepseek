import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs

set_option linter.unusedVariables false

namespace Work.HP.MDEstimates.hiparts

/-- `conv_AQ_T1`: the `hiCell`-type term `32 · 2^53 · B^{6+1/1000} Δ² M^53 · (A^{68-k} B^{2k-8} Δ^{-k})`
is at most `hiK/2 · hiTgt A B` whenever the corresponding logarithmic linear form is at most
`2000 - 59 log 2`.  The proof is a pure power/exponent computation: after combining the powers of
`B` and of `Δ` and splitting `A^{68-k} = A^{2175/32} · A^{1/32-k}` the left-hand side becomes
`2^58 · hiTgt A B · exp L` with `L` the linear form of the hypothesis, and
`exp L ≤ exp (2000 - 59 log 2) = hiK/2^59`. -/
theorem conv_AQ_T1 (A B Δ M : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M) (k : ℕ)
    (hk : 4 ≤ k) (hk67 : k ≤ 67)
    (h : (1/32 - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 3.999 + 1/1000) * Real.log B
        + (2 - (k:ℝ)) * Real.log Δ + 53 * Real.log M ≤ 2000 - 59 * Real.log 2) :
    32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53
        * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ)))
      ≤ hiK / 2 * hiTgt A B := by
  have hA2 : A ^ ((2175:ℝ)/32) * A ^ ((1:ℝ)/32 - (k:ℝ)) = A ^ ((68:ℝ) - (k:ℝ)) := by
    rw [← Real.rpow_add hA]; congr 1; ring
  have hB2 : B ^ (6 + (1:ℝ)/1000) * B ^ (2*(k:ℝ) - 8)
      = B ^ ((1999:ℝ)/1000) * B ^ (2*(k:ℝ) - 3.999 + 1/1000) := by
    rw [← Real.rpow_add hB]
    rw [show (6 + (1:ℝ)/1000) + (2*(k:ℝ) - 8)
          = (1999:ℝ)/1000 + (2*(k:ℝ) - 3.999 + 1/1000) by ring]
    rw [Real.rpow_add hB]
  have hΔ2 : Δ ^ 2 * Δ ^ (-(k:ℝ)) = Δ ^ (2 - (k:ℝ)) := by
    rw [← Real.rpow_natCast Δ 2, ← Real.rpow_add hΔ]
    congr 1
  have h2_53 : (32:ℝ) * 2^53 = (2:ℝ)^58 := by norm_num
  have hEq : 32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53
        * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ)))
      = (2:ℝ)^58 * hiTgt A B
        * (A ^ ((1:ℝ)/32 - (k:ℝ)) * B ^ (2*(k:ℝ) - 3.999 + 1/1000) * Δ ^ (2 - (k:ℝ)) * M ^ 53) := by
    calc 32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53
          * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ)))
        = (32 * 2^53) * (B ^ (6 + (1:ℝ)/1000) * B ^ (2*(k:ℝ) - 8))
            * (Δ^2 * Δ ^ (-(k:ℝ))) * M^53 * A ^ ((68:ℝ) - (k:ℝ)) := by ring
      _ = (32 * 2^53) * (B ^ ((1999:ℝ)/1000) * B ^ (2*(k:ℝ) - 3.999 + 1/1000))
            * Δ ^ (2 - (k:ℝ)) * M^53 * A ^ ((68:ℝ) - (k:ℝ)) := by rw [hB2, hΔ2]
      _ = (32 * 2^53) * (B ^ ((1999:ℝ)/1000) * B ^ (2*(k:ℝ) - 3.999 + 1/1000))
            * Δ ^ (2 - (k:ℝ)) * M^53 * (A ^ ((2175:ℝ)/32) * A ^ ((1:ℝ)/32 - (k:ℝ))) := by rw [← hA2]
      _ = (2:ℝ)^58 * hiTgt A B
            * (A ^ ((1:ℝ)/32 - (k:ℝ)) * B ^ (2*(k:ℝ) - 3.999 + 1/1000) * Δ ^ (2 - (k:ℝ)) * M ^ 53) := by
          rw [h2_53]; unfold hiTgt; ring
  have eA : A ^ ((1:ℝ)/32 - (k:ℝ)) = Real.exp (((1:ℝ)/32 - (k:ℝ)) * Real.log A) := by
    rw [Real.rpow_def_of_pos hA, mul_comm]
  have eB : B ^ (2*(k:ℝ) - 3.999 + 1/1000) = Real.exp ((2*(k:ℝ) - 3.999 + 1/1000) * Real.log B) := by
    rw [Real.rpow_def_of_pos hB, mul_comm]
  have eΔ : Δ ^ (2 - (k:ℝ)) = Real.exp ((2 - (k:ℝ)) * Real.log Δ) := by
    rw [Real.rpow_def_of_pos hΔ, mul_comm]
  have eM : M ^ 53 = Real.exp (53 * Real.log M) := by
    rw [show (53:ℝ) * Real.log M = ((53:ℕ):ℝ) * Real.log M by norm_num, Real.exp_nat_mul,
        Real.exp_log hM]
  have hE : Real.exp (2000 - 59 * Real.log 2) = hiK / (2:ℝ)^59 := by
    rw [Real.exp_sub, hiK]
    congr 1
    rw [show (59:ℝ) * Real.log 2 = ((59:ℕ):ℝ) * Real.log 2 by norm_num, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hP : A ^ ((1:ℝ)/32 - (k:ℝ)) * B ^ (2*(k:ℝ) - 3.999 + 1/1000) * Δ ^ (2 - (k:ℝ)) * M ^ 53
      ≤ hiK / (2:ℝ)^59 := by
    have hexp : A ^ ((1:ℝ)/32 - (k:ℝ)) * B ^ (2*(k:ℝ) - 3.999 + 1/1000) * Δ ^ (2 - (k:ℝ)) * M ^ 53
        = Real.exp ((1/32 - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 3.999 + 1/1000) * Real.log B
            + (2 - (k:ℝ)) * Real.log Δ + 53 * Real.log M) := by
      rw [eA, eB, eΔ, eM, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    rw [hexp]
    calc Real.exp ((1/32 - (k:ℝ)) * Real.log A + (2*(k:ℝ) - 3.999 + 1/1000) * Real.log B
            + (2 - (k:ℝ)) * Real.log Δ + 53 * Real.log M)
        ≤ Real.exp (2000 - 59 * Real.log 2) := Real.exp_le_exp.mpr h
      _ = hiK / (2:ℝ)^59 := hE
  rw [hEq]
  have hnn : 0 ≤ (2:ℝ)^58 * hiTgt A B := by
    have := hiTgt_pos hA hB; positivity
  calc (2:ℝ)^58 * hiTgt A B
        * (A ^ ((1:ℝ)/32 - (k:ℝ)) * B ^ (2*(k:ℝ) - 3.999 + 1/1000) * Δ ^ (2 - (k:ℝ)) * M ^ 53)
      ≤ (2:ℝ)^58 * hiTgt A B * (hiK / (2:ℝ)^59) := mul_le_mul_of_nonneg_left hP hnn
    _ = hiK / 2 * hiTgt A B := by
        rw [show (2:ℝ)^58 * hiTgt A B * (hiK / (2:ℝ)^59)
              = (2:ℝ)^58 * (hiK / (2:ℝ)^59) * hiTgt A B by ring]
        have h2 : (2:ℝ)^58 * (hiK / (2:ℝ)^59) = hiK / 2 := by
          rw [div_eq_mul_inv,
              show (2:ℝ)^58 * (hiK * ((2:ℝ)^59)⁻¹) = ((2:ℝ)^58 * ((2:ℝ)^59)⁻¹) * hiK by ring]
          rw [show (2:ℝ)^58 * ((2:ℝ)^59)⁻¹ = 1/2 by norm_num]
          ring
        rw [h2]

end Work.HP.MDEstimates.hiparts
