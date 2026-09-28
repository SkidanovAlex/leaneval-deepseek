import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiCellDefs

namespace Work.HP.MDEstimates.hiparts

theorem hi_dyadic_idx (A B d : ℝ) (hA : 0 < A)
    (hd0 : A ^ ((1 : ℝ) / 20) ≤ d) (hd48 : d ≤ 48 * B ^ 2 / A) :
    hiDelta A (hiIdx A d) ≤ d ∧ d < 2 * hiDelta A (hiIdx A d) ∧ hiIdx A d ≤ hiI A B := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hc_pos : 0 < A ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hA _
  have hd_pos : 0 < d := lt_of_lt_of_le hc_pos hd0
  have hx_pos : 0 < d / A ^ ((1 : ℝ) / 20) := div_pos hd_pos hc_pos
  have hx_ge1 : 1 ≤ d / A ^ ((1 : ℝ) / 20) := by
    rw [le_div_iff₀ hc_pos]
    simpa using hd0
  have hlog_nonneg : 0 ≤ Real.logb 2 (d / A ^ ((1 : ℝ) / 20)) :=
    Real.logb_nonneg htwo hx_ge1
  set n := ⌊Real.logb 2 (d / A ^ ((1 : ℝ) / 20))⌋₊ with hn_def
  have hidx : hiIdx A d = n := by rw [hiIdx, hn_def]
  have h2n : (2 : ℝ) ^ n ≤ d / A ^ ((1 : ℝ) / 20) := by
    have h1 : (n : ℝ) ≤ Real.logb 2 (d / A ^ ((1 : ℝ) / 20)) := by
      rw [hn_def]; exact Nat.floor_le hlog_nonneg
    have h2 := (Real.le_logb_iff_rpow_le htwo hx_pos).mp h1
    rwa [Real.rpow_natCast] at h2
  have hpart1 : hiDelta A (hiIdx A d) ≤ d := by
    rw [hidx, hiDelta]
    calc A ^ ((1 : ℝ) / 20) * 2 ^ n
        ≤ A ^ ((1 : ℝ) / 20) * (d / A ^ ((1 : ℝ) / 20)) :=
          mul_le_mul_of_nonneg_left h2n hc_pos.le
      _ = d := mul_div_cancel₀ d hc_pos.ne'
  have hpart2 : d < 2 * hiDelta A (hiIdx A d) := by
    rw [hidx, hiDelta]
    have hlt : Real.logb 2 (d / A ^ ((1 : ℝ) / 20)) < (n : ℝ) + 1 := by
      rw [hn_def]; exact Nat.lt_floor_add_one _
    have h2 := (Real.logb_lt_iff_lt_rpow htwo hx_pos).mp hlt
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (n : ℝ) 1, Real.rpow_one,
      Real.rpow_natCast] at h2
    have h3 := mul_lt_mul_of_pos_left h2 hc_pos
    rw [mul_div_cancel₀ d hc_pos.ne'] at h3
    calc d < A ^ ((1 : ℝ) / 20) * (2 ^ n * 2) := h3
      _ = 2 * (A ^ ((1 : ℝ) / 20) * 2 ^ n) := by ring
  have hA21 : A ^ ((21 : ℝ) / 20) = A * A ^ ((1 : ℝ) / 20) := by
    have h : (21 : ℝ) / 20 = 1 + 1 / 20 := by norm_num
    rw [h, Real.rpow_add hA, Real.rpow_one]
  have hx_le : d / A ^ ((1 : ℝ) / 20) ≤ 48 * B ^ 2 / A ^ ((21 : ℝ) / 20) := by
    have h1 : d / A ^ ((1 : ℝ) / 20) ≤ (48 * B ^ 2 / A) / A ^ ((1 : ℝ) / 20) :=
      div_le_div_of_nonneg_right hd48 hc_pos.le
    rw [div_div, ← hA21] at h1
    exact h1
  have hlog_le : Real.logb 2 (d / A ^ ((1 : ℝ) / 20))
      ≤ Real.logb 2 (48 * B ^ 2 / A ^ ((21 : ℝ) / 20)) :=
    Real.logb_le_logb_of_le htwo hx_pos hx_le
  have hpart3 : hiIdx A d ≤ hiI A B := by
    rw [hidx, hiI, hn_def]
    exact le_trans (Nat.floor_mono hlog_le) (Nat.floor_le_ceil _)
  exact ⟨hpart1, hpart2, hpart3⟩

end Work.HP.MDEstimates.hiparts
