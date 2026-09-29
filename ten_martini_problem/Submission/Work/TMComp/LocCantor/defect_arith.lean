import Mathlib

namespace Work.TMComp.LocCantor

theorem defect_arith (R q X : ℝ) (hR : 1 ≤ R) (hq : R ^ 2 + 2 + (R⁻¹) ^ 2 ≤ q)
    (hX : q - 2 ≤ X) : R ^ 2 / 4 * X ≤ 2 + q * (X - 2) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hRinv : R * R⁻¹ = 1 := mul_inv_cancel₀ hRne
  have e1 : R ^ 2 * (R⁻¹) ^ 2 = 1 := by rw [← mul_pow, hRinv, one_pow]
  have hc : 0 ≤ q - R ^ 2 / 4 := by nlinarith [hq, sq_nonneg R, sq_nonneg R⁻¹]
  have hX' : 0 ≤ X - (q - 2) := by linarith
  have hd : 0 ≤ 2 - 2 * q + (q - R ^ 2 / 4) * (q - 2) := by
    set qm := R ^ 2 + 2 + (R⁻¹) ^ 2 with hqm
    have hle : qm ≤ q := hq
    have hsum : 0 ≤ q + qm - 4 - R ^ 2 / 4 := by
      nlinarith [hle, hqm, sq_nonneg R, sq_nonneg R⁻¹]
    have hR4 : (1 : ℝ) ≤ R ^ 4 := one_le_pow₀ hR
    have h4 : (0 : ℝ) ≤ (R⁻¹) ^ 4 :=
      pow_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ R)) 4
    have hEmid : (2 - 2 * qm + (qm - R ^ 2 / 4) * (qm - 2)) =
        (3 / 4 : ℝ) * R ^ 4 + (R⁻¹) ^ 4 - 1 / 4 := by
      rw [hqm]; nlinarith [e1]
    have hEm : 0 ≤ 2 - 2 * qm + (qm - R ^ 2 / 4) * (qm - 2) := by
      rw [hEmid]; nlinarith [hR4, h4]
    have key : (2 - 2 * q + (q - R ^ 2 / 4) * (q - 2)) =
        (2 - 2 * qm + (qm - R ^ 2 / 4) * (qm - 2)) +
          (q - qm) * (q + qm - 4 - R ^ 2 / 4) := by ring
    have hdq : 0 ≤ q - qm := by linarith
    have hprod2 : 0 ≤ (q - qm) * (q + qm - 4 - R ^ 2 / 4) := mul_nonneg hdq hsum
    linarith [key, hEm, hprod2]
  have hprod : 0 ≤ (q - R ^ 2 / 4) * (X - (q - 2)) := mul_nonneg hc hX'
  nlinarith [hprod, hd]

end Work.TMComp.LocCantor
