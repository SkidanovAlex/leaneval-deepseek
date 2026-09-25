import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.Real

theorem exp_mul_le_of_le_div {v w t ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hv : 1 ≤ v) (hw : 0 ≤ w) (hvw : 3628800 * w ≤ v ^ 9) (ht : v / ε ≤ t) : w * t / ε ≤ Real.exp t := by
  have hN : (0 : ℝ) < 3628800 := by norm_num
  have hv_pos : 0 < v := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le (div_pos hv_pos hε) ht
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hε_nonneg : 0 ≤ ε := hε.le
  have hε8 : ε ^ 8 ≤ (1 : ℝ) := pow_le_one₀ hε_nonneg hε1
  have hw_le : w ≤ v ^ 9 / 3628800 := by
    rw [le_div_iff₀ hN]
    linarith [hvw]
  have hx_nonneg : 0 ≤ v / ε := by positivity
  have hx9 : (v / ε) ^ 9 ≤ t ^ 9 := pow_le_pow_left₀ hx_nonneg ht 9
  have hmid : (v / ε) ^ 9 * ε ^ 8 ≤ t ^ 9 * 1 :=
    mul_le_mul hx9 hε8 (by positivity) (by positivity)
  calc
    w * t / ε = w * (t / ε) := by ring
    _ ≤ (v ^ 9 / 3628800) * (t / ε) := by
        exact mul_le_mul_of_nonneg_right hw_le (by positivity)
    _ = (v / ε) ^ 9 * ε ^ 8 * t / 3628800 := by
        field_simp
    _ ≤ t ^ 9 * 1 * t / 3628800 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmid ht_nonneg) hN.le
    _ = t ^ 10 / 3628800 := by ring
    _ ≤ Real.exp t := by
        have h := Real.pow_div_factorial_le_exp t ht_nonneg 10
        norm_num at h
        exact h

end Commons.Analysis.Real