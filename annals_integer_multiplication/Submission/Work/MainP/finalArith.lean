import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic

/-!
# `Work.MainP.finalArith`: the final error bookkeeping of Proposition 5.3

`2 S (3·2^{γ+5} T L + 2) + 3 < 2^{γ+8} T² L` with `γ = 2·D·α²`, `S ≤ T`, `T ≥ 3` and
`L = ⌊log₂ T⌋`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

theorem finalArith (S T α L : ℕ) (hS : S ≤ T) (hT : 3 ≤ T) (hlog : L = Nat.log 2 T) :
    (2 * (S : ℝ) * (3 * ((2 ^ (2 * HvdH.D * α ^ 2 + 5) * T * L : ℕ) : ℝ) + 2) + 3)
      < ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * T ^ 2 * L : ℕ) : ℝ) := by
  subst hlog
  have hL1 : 1 ≤ Nat.log 2 T := by
    have h := Nat.log_pos (b := 2) (n := T) (by norm_num) (by omega)
    omega
  have hcast1 : ((2 ^ (2 * HvdH.D * α ^ 2 + 5) * T * Nat.log 2 T : ℕ) : ℝ)
      = (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) * (T : ℝ) * (Nat.log 2 T : ℝ) := by
    push_cast [Nat.cast_pow]; ring
  have hcast2 : ((2 ^ (2 * HvdH.D * α ^ 2 + 8) * T ^ 2 * Nat.log 2 T : ℕ) : ℝ)
      = (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 8) * (T : ℝ) ^ 2 * (Nat.log 2 T : ℝ) := by
    push_cast [Nat.cast_pow]; ring
  rw [hcast1, hcast2]
  have hpow : (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 8)
      = 8 * (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) := by
    rw [show 2 * HvdH.D * α ^ 2 + 8 = (2 * HvdH.D * α ^ 2 + 5) + 3 by ring, pow_add]
    norm_num
    ring
  rw [hpow]
  have hc32 : (32 : ℝ) ≤ (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) := by
    calc (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
      _ ≤ (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
  have hSr : (S : ℝ) ≤ (T : ℝ) := by exact_mod_cast hS
  have hTr : (3 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hLr : (1 : ℝ) ≤ (Nat.log 2 T : ℝ) := by exact_mod_cast hL1
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := by linarith
  have hT2 : 3 * (T : ℝ) ≤ (T : ℝ) ^ 2 * (Nat.log 2 T : ℝ) := by nlinarith
  have hbig : 4 * (T : ℝ) + 3
      < 2 * (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) * (T : ℝ) ^ 2 * (Nat.log 2 T : ℝ) := by
    nlinarith [hc32, hTr, hT2]
  have hcTL : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) * (T : ℝ) * (Nat.log 2 T : ℝ) := by
    positivity
  have hST : (S : ℝ) * ((2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) * (T : ℝ) * (Nat.log 2 T : ℝ))
      ≤ (T : ℝ) * ((2 : ℝ) ^ (2 * HvdH.D * α ^ 2 + 5) * (T : ℝ) * (Nat.log 2 T : ℝ)) :=
    mul_le_mul_of_nonneg_right hSr hcTL
  nlinarith [hbig, hSr, hcTL, hST]

end Work.MainP
