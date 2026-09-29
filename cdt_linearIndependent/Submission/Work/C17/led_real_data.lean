import Mathlib
import Submission.Work.C17.local_exp_data

namespace Work.C17

theorem led_real_data (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) :
    (2 : ℝ) < ledC a b ∧ (2 : ℝ) < ledD a b ∧ ledC a b ≠ ledD a b ∧
      ledC a b + ledD a b = 4 * (a : ℝ) * (b : ℝ) ∧
      ledC a b * ledD a b + 2 = 4 * (a : ℝ) ^ 2 + 4 * (b : ℝ) ^ 2 - 2 := by
  have hA : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hB : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have habR : (a : ℝ) ≠ (b : ℝ) := by exact_mod_cast hab
  have hDpos : 0 < ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) :=
    mul_pos (by nlinarith : (0 : ℝ) < (a : ℝ) ^ 2 - 1)
      (by nlinarith : (0 : ℝ) < (b : ℝ) ^ 2 - 1)
  have hDnn : 0 ≤ ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) := le_of_lt hDpos
  have hspos : 0 < Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) :=
    Real.sqrt_pos.mpr hDpos
  have hsum : ledC a b + ledD a b = 4 * (a : ℝ) * (b : ℝ) := by
    unfold ledC ledD; ring
  have hprod : ledC a b * ledD a b + 2 = 4 * (a : ℝ) ^ 2 + 4 * (b : ℝ) ^ 2 - 2 := by
    unfold ledC ledD
    nlinarith [Real.sq_sqrt hDnn]
  have hC : (2 : ℝ) < ledC a b := by
    unfold ledC
    have : (2 : ℝ) < 2 * (a : ℝ) * (b : ℝ) := by nlinarith
    nlinarith [Real.sqrt_nonneg (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1))]
  have hD : (2 : ℝ) < ledD a b := by
    have hsq : 0 < ((a : ℝ) - (b : ℝ)) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr habR)
    have hprod2 : ((a : ℝ) * (b : ℝ) - 1) ^ 2 > ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) := by
      nlinarith
    have hposy : (0 : ℝ) < (a : ℝ) * (b : ℝ) - 1 := by nlinarith
    have hlt : Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) < (a : ℝ) * (b : ℝ) - 1 := by
      rw [Real.sqrt_lt' hposy]
      exact hprod2
    unfold ledD
    linarith
  have hne : ledC a b ≠ ledD a b := by
    intro h
    have hzero : Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) = 0 := by
      unfold ledC ledD at h
      linarith
    linarith [hspos, hzero]
  exact ⟨hC, hD, hne, hsum, hprod⟩

end Work.C17
