import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs
import Submission.Work.HP.MDEstimates.hiparts.HiArithDefs
import Submission.Work.HP.MDEstimates.hiparts.HiCore
import Submission.Work.HP.MDEstimates.hiparts.log_sq_le
import Submission.Work.HP.MDEstimates.hiparts.hiLZ_le_A_P
import Submission.Work.HP.MDEstimates.hiparts.hiLZ_le_A_Q
import Submission.Work.HP.MDEstimates.hiparts.hiLZ_le_B_P
import Submission.Work.HP.MDEstimates.hiparts.hiLZ_le_B_Q
import Submission.Work.HP.MDEstimates.hiparts.conv_AP_T1
import Submission.Work.HP.MDEstimates.hiparts.conv_AP_T2
import Submission.Work.HP.MDEstimates.hiparts.conv_AQ_T1
import Submission.Work.HP.MDEstimates.hiparts.conv_AQ_T2
import Submission.Work.HP.MDEstimates.hiparts.conv_BP_T1
import Submission.Work.HP.MDEstimates.hiparts.conv_BP_T2
import Submission.Work.HP.MDEstimates.hiparts.conv_BQ_T1
import Submission.Work.HP.MDEstimates.hiparts.conv_BQ_T2

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.HP.MDEstimates.hiparts

/-! ## Elementary analytic bounds -/

/-- `log X ≤ X/400 + 400` for `X > 0` (from `log X ≤ 2√X ≤ X/400 + 400`). -/
lemma hc_log_le_div_add (X : ℝ) (hX : 0 < X) : Real.log X ≤ X / 400 + 400 := by
  have h1 : Real.log X ≤ 2 * Real.sqrt X := by
    have h := Real.log_le_rpow_div (le_of_lt hX) (show (0:ℝ) < 1/2 by norm_num)
    rw [div_eq_mul_inv, show (1/2 : ℝ)⁻¹ = 2 by norm_num, mul_comm] at h
    rwa [Real.sqrt_eq_rpow]
  have h2 : 2 * Real.sqrt X ≤ X / 400 + 400 := by
    have hsq := Real.sq_sqrt (le_of_lt hX)
    have hnn : (0:ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
    nlinarith [sq_nonneg (Real.sqrt X - 400)]
  linarith

lemma hc_log_two_le_07 : Real.log 2 ≤ 7/10 := by
  have h := Real.log_two_lt_d9
  linarith

lemma hc_log_128_le : Real.log 128 ≤ 5 := by
  have h : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have h2 := hc_log_two_le_07
  linarith

/-- branch `2Δ ≤ (2M)^53` in logarithmic form -/
lemma hc_branchP_log {Δ M : ℝ} (hΔ : 0 < Δ) (hM : 0 < M) (h : 2 * Δ ≤ (2 * M) ^ 53) :
    Real.log Δ ≤ 53 * Real.log M + 52 * Real.log 2 := by
  have h1 : Real.log (2 * Δ) ≤ Real.log ((2 * M) ^ 53) := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by norm_num) (ne_of_gt hΔ), Real.log_pow] at h1
  rw [Real.log_mul (by norm_num) (ne_of_gt hM)] at h1
  push_cast at h1
  linarith

/-- branch `(2M)^53 ≤ 2Δ` in logarithmic form -/
lemma hc_branchQ_log {Δ M : ℝ} (hΔ : 0 < Δ) (hM : 0 < M) (h : (2 * M) ^ 53 ≤ 2 * Δ) :
    53 * Real.log M + 52 * Real.log 2 ≤ Real.log Δ := by
  have h1 : Real.log ((2 * M) ^ 53) ≤ Real.log (2 * Δ) := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by norm_num) (ne_of_gt hΔ), Real.log_pow] at h1
  rw [Real.log_mul (by norm_num) (ne_of_gt hM)] at h1
  push_cast at h1
  linarith

/-! ## Absorbing the `(log 4Δ)²` factor into the margin `B^{1/1000}` -/

lemma hc_absorb_AP (B Δ : ℝ) (hB : 0 < B) (hΔ : 0 < Δ)
    (hl : (Real.log (4 * Δ)) ^ 2 ≤ B ^ ((1:ℝ)/1000)) :
    64 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 ≤ 64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3 := by
  have hpos : (0:ℝ) ≤ 64 * B ^ 6 * Δ ^ 3 := by positivity
  calc 64 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2
      ≤ 64 * B ^ 6 * Δ ^ 3 * B ^ ((1:ℝ)/1000) := mul_le_mul_of_nonneg_left hl hpos
    _ = 64 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 3 := by
        have h6 : B ^ (6:ℝ) = B ^ 6 := Real.rpow_natCast B 6
        rw [show (64:ℝ) * B ^ 6 * Δ ^ 3 * B ^ ((1:ℝ)/1000)
              = 64 * (B ^ 6 * B ^ ((1:ℝ)/1000)) * Δ ^ 3 by ring]
        rw [← h6, ← Real.rpow_add hB]

lemma hc_absorb_AQ (B Δ M : ℝ) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 ≤ M)
    (hl : (Real.log (4 * Δ)) ^ 2 ≤ B ^ ((1:ℝ)/1000)) :
    32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 * (Real.log (4 * Δ)) ^ 2
      ≤ 32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53 := by
  have hpos : (0:ℝ) ≤ 32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 := by positivity
  calc 32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 * (Real.log (4 * Δ)) ^ 2
      ≤ 32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 * B ^ ((1:ℝ)/1000) :=
        mul_le_mul_of_nonneg_left hl hpos
    _ = 32 * 2 ^ 53 * B ^ (6 + (1:ℝ)/1000) * Δ ^ 2 * M ^ 53 := by
        have h6 : B ^ (6:ℝ) = B ^ 6 := Real.rpow_natCast B 6
        rw [show 32 * 2 ^ 53 * B ^ 6 * Δ ^ 2 * M ^ 53 * B ^ ((1:ℝ)/1000)
              = 32 * 2 ^ 53 * (B ^ 6 * B ^ ((1:ℝ)/1000)) * Δ ^ 2 * M ^ 53 by ring]
        rw [← h6, ← Real.rpow_add hB]

lemma hc_absorb_BP (B Δ : ℝ) (hB : 0 < B) (hΔ : 0 < Δ)
    (hl : (Real.log (4 * Δ)) ^ 2 ≤ B ^ ((1:ℝ)/1000)) :
    64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) * (Real.log (4 * Δ)) ^ 2
      ≤ 64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2) := by
  have hpos : (0:ℝ) ≤ 64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) := by positivity
  calc 64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) * (Real.log (4 * Δ)) ^ 2
      ≤ 64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) * B ^ ((1:ℝ)/1000) :=
        mul_le_mul_of_nonneg_left hl hpos
    _ = 64 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((9:ℝ)/2) := by
        rw [show 64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) * B ^ ((1:ℝ)/1000)
              = 64 * (B ^ ((9:ℝ)/2) * B ^ ((1:ℝ)/1000)) * Δ ^ ((9:ℝ)/2) by ring]
        rw [← Real.rpow_add hB]

lemma hc_absorb_BQ (B Δ M : ℝ) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 ≤ M)
    (hl : (Real.log (4 * Δ)) ^ 2 ≤ B ^ ((1:ℝ)/1000)) :
    32 * 2 ^ 53 * B ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) * M ^ 53 * (Real.log (4 * Δ)) ^ 2
      ≤ 32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53 := by
  have hpos : (0:ℝ) ≤ 32 * 2 ^ 53 * B ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) * M ^ 53 := by positivity
  calc 32 * 2 ^ 53 * B ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) * M ^ 53 * (Real.log (4 * Δ)) ^ 2
      ≤ 32 * 2 ^ 53 * B ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) * M ^ 53 * B ^ ((1:ℝ)/1000) :=
        mul_le_mul_of_nonneg_left hl hpos
    _ = 32 * 2 ^ 53 * B ^ ((9:ℝ)/2 + (1:ℝ)/1000) * Δ ^ ((7:ℝ)/2) * M ^ 53 := by
        rw [show 32 * 2 ^ 53 * B ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) * M ^ 53 * B ^ ((1:ℝ)/1000)
              = 32 * 2 ^ 53 * (B ^ ((9:ℝ)/2) * B ^ ((1:ℝ)/1000)) * Δ ^ ((7:ℝ)/2) * M ^ 53
              by ring]
        rw [← Real.rpow_add hB]

/-! ## Assembly -/

lemma hc_assemble (A B Δ M Lb : ℝ) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 < M)
    (hLb : hiLZ B (2 * Δ) (2 * M) ≤ Lb) (k : ℕ) (hk : k ∈ Finset.Icc 4 67)
    (h1 : Lb * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ (2*(k:ℝ) - 8) * Δ ^ (-(k:ℝ)))
        ≤ hiK / 2 * hiTgt A B)
    (h2 : Lb * (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) ≤ hiK / 2 * hiTgt A B) :
    hiLZ B (2 * Δ) (2 * M) * hiMin A B Δ M
      ≤ hiK * A ^ ((68:ℝ) - 1/32) * B ^ 2 * B ^ (-(1/1000:ℝ)) := by
  have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk67 : k ≤ 67 := (Finset.mem_Icc.mp hk).2
  have hmin : hiMin A B Δ M ≤ hiCell A B Δ M k := hiMin_le_cell A B Δ M hk4 hk67
  have hminnn : (0:ℝ) ≤ hiMin A B Δ M := hiMin_nonneg A B Δ M hA.le hB.le hΔ.le hM
  have hLZnn : (0:ℝ) ≤ hiLZ B (2 * Δ) (2 * M) := by
    unfold hiLZ; positivity
  have hLbnn : (0:ℝ) ≤ Lb := le_trans hLZnn hLb
  have hAMpos : (0:ℝ) < 2 * A / M := by positivity
  -- rewrite `hiCell` in terms of real powers
  have hAk : ((68 - k : ℕ) : ℝ) = (68:ℝ) - (k:ℝ) := Nat.cast_sub (by omega)
  have eA : A ^ ((68:ℝ) - (k:ℝ)) = A ^ (68 - k) := by
    rw [← Real.rpow_natCast A (68 - k), hAk]
  have hBk : ((2 * k - 8 : ℕ) : ℝ) = (2:ℝ) * (k:ℝ) - 8 := by
    have h1 : 8 ≤ 2 * k := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have eB : B ^ ((2:ℝ)*(k:ℝ) - 8) = B ^ (2 * k - 8) := by
    rw [← Real.rpow_natCast B (2 * k - 8), hBk]
  have hMk : ((67 - k : ℕ) : ℝ) = (67:ℝ) - (k:ℝ) := Nat.cast_sub hk67
  have eM : (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) = (2 * A / M) ^ (67 - k) := by
    rw [← Real.rpow_natCast (2 * A / M) (67 - k), hMk]
  have hcell : hiCell A B Δ M k
      = A ^ ((68:ℝ) - (k:ℝ)) * B ^ ((2:ℝ)*(k:ℝ) - 8) * Δ ^ (-(k:ℝ))
        + (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) := by
    unfold hiCell
    rw [eA, eB, eM]
  calc hiLZ B (2 * Δ) (2 * M) * hiMin A B Δ M
      ≤ Lb * hiCell A B Δ M k := mul_le_mul hLb hmin hminnn hLbnn
    _ = Lb * (A ^ ((68:ℝ) - (k:ℝ)) * B ^ ((2:ℝ)*(k:ℝ) - 8) * Δ ^ (-(k:ℝ)))
          + Lb * (2 * A / M) ^ ((67:ℝ) - (k:ℝ)) := by rw [hcell]; ring
    _ ≤ hiK / 2 * hiTgt A B + hiK / 2 * hiTgt A B := add_le_add h1 h2
    _ = hiK * A ^ ((68:ℝ) - 1/32) * B ^ 2 * B ^ (-(1/1000:ℝ)) := by
        unfold hiTgt
        rw [show ((1999:ℝ)/1000) = 2 + -(1/1000) by norm_num, Real.rpow_add hB,
            show ((2175:ℝ)/32) = 68 - 1/32 by norm_num,
            show (B:ℝ) ^ (2:ℝ) = B ^ 2 from Real.rpow_natCast B 2]
        ring

end Work.HP.MDEstimates.hiparts
