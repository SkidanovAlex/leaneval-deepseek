import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.SpecialFunctions.Log

/-- For `1 ≤ t ≤ 16`, the lower bound `log t ≥ (t - 1) / 16`. -/
lemma log_ge_sub_one_div (t : ℝ) (ht1 : 1 ≤ t) (ht16 : t ≤ 16) :
    (t - 1) / 16 ≤ Real.log t := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hA : (t - 1) / 16 ≤ 1 - 1 / t := by
    have hcalc : (1 - 1 / t) - (t - 1) / 16 = ((t - 1) * (16 - t)) / (16 * t) := by
      field_simp [htpos.ne']
    have hnum : 0 ≤ ((t - 1) * (16 - t)) / (16 * t) := by
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht16)) (by positivity)
    have hnonneg : 0 ≤ (1 - 1 / t) - (t - 1) / 16 := by
      rw [hcalc]
      exact hnum
    linarith
  have hB : 1 - 1 / t ≤ Real.log t := by
    have hle : Real.log (t⁻¹) ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
    have hneg : -Real.log t ≤ t⁻¹ - 1 := by
      simpa [Real.log_inv] using hle
    have hb : 1 - t⁻¹ ≤ Real.log t := by linarith
    simpa [one_div] using hb
  exact hA.trans hB

theorem log_strip_bound_A_nonneg (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 8) :
    Real.log 2 + (3 : ℝ) / 2 - Real.log x - (1 : ℝ) / (2 * x) ≥ 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have ht1 : 1 ≤ 8 / x := by
    rw [le_div_iff₀ hxpos]
    simpa using hx2
  have ht16 : 8 / x ≤ 16 := by
    have ht8 : 8 / x ≤ 8 := (div_le_iff₀ hxpos).2 (by nlinarith)
    linarith
  have hbound : (8 / x - 1) / 16 ≤ Real.log (8 / x) :=
    log_ge_sub_one_div (8 / x) ht1 ht16
  have hlog8x : Real.log (8 / x) = Real.log 8 - Real.log x := by
    exact Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hxpos)
  have hrhs : (8 / x - 1) / 16 = 1 / (2 * x) - 1 / 16 := by
    field_simp [hxpos.ne']
    ring
  have hmono : Real.log x + 1 / (2 * x) ≤ Real.log 8 + 1 / 16 := by
    rw [hlog8x, hrhs] at hbound
    linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num
  have hlog2 : Real.log 2 ≤ (23 : ℝ) / 32 := by
    have hlt := Real.log_two_lt_d9
    have hnum : (0.6931471808 : ℝ) < (23 : ℝ) / 32 := by norm_num
    exact le_of_lt (lt_trans hlt hnum)
  have h2log : 2 * Real.log 2 ≤ (23 : ℝ) / 16 := by
    calc
      2 * Real.log 2 ≤ 2 * ((23 : ℝ) / 32) := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ = (23 : ℝ) / 16 := by ring
  have h8le : Real.log 8 + 1 / 16 ≤ Real.log 2 + (3 : ℝ) / 2 := by
    rw [hlog8]
    linarith
  linarith

end Commons.Analysis.SpecialFunctions.Log