import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

theorem le_sqrt_mul_rpow_neg_sixth {M : ℕ} {l : ℝ} (hM : 1 ≤ M) (hl : 0 < l)
    (hlm : (M : ℝ) ^ 3 * l ≤ 1) :
    (M : ℝ) ≤ Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ)) := by
  let m : ℝ := (M : ℝ)
  have hM1 : (1 : ℝ) ≤ m := by
    dsimp [m]
    exact_mod_cast hM
  have hm_nonneg : 0 ≤ m := by linarith
  have hm_pos : 0 < m := lt_of_lt_of_le (by norm_num) hM1
  have hl_nonneg : 0 ≤ l := le_of_lt hl
  have hlne : l ≠ 0 := ne_of_gt hl
  -- From `m^3 * l ≤ 1` get `m^3 ≤ l⁻¹`
  have h3 : m ^ 3 ≤ l⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_right hlm (inv_nonneg.mpr hl_nonneg)
    calc
      m ^ 3 = (m ^ 3 * l) * l⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hlne, mul_one]
      _ ≤ 1 * l⁻¹ := hstep
      _ = l⁻¹ := by rw [one_mul]
  -- From that get `m^6 ≤ m^3 * l⁻¹`
  have hm3_nonneg : 0 ≤ m ^ 3 := by positivity
  have hmain : m ^ 6 ≤ m ^ 3 * l⁻¹ := by
    calc
      m ^ 6 = m ^ 3 * m ^ 3 := by ring
      _ ≤ m ^ 3 * l⁻¹ := mul_le_mul_of_nonneg_left h3 hm3_nonneg
  -- Compute the sixth power of the right-hand side
  have hsqrt : (Real.sqrt m) ^ 6 = m ^ 3 := by
    calc
      (Real.sqrt m) ^ 6 = ((Real.sqrt m) ^ 2) ^ 3 := by ring
      _ = m ^ 3 := by rw [Real.sq_sqrt hm_nonneg]
  have hlpow : (l ^ (-(1 / 6 : ℝ))) ^ 6 = l⁻¹ := by
    calc
      (l ^ (-(1 / 6 : ℝ))) ^ 6 = (l ^ (-(1 / 6 : ℝ))) ^ (6 : ℝ) :=
        (Real.rpow_natCast (l ^ (-(1 / 6 : ℝ))) 6).symm
      _ = l⁻¹ := by
        rw [← Real.rpow_mul hl_nonneg (-(1 / 6 : ℝ)) (6 : ℝ)]
        norm_num
        rw [Real.rpow_neg_one]
  have hpow6 : (Real.sqrt m * l ^ (-(1 / 6 : ℝ))) ^ 6 = m ^ 3 * l⁻¹ := by
    rw [mul_pow, hsqrt, hlpow]
  -- Raise both sides to the sixth power and compare
  have hgoal6 : m ^ 6 ≤ (Real.sqrt m * l ^ (-(1 / 6 : ℝ))) ^ 6 := by
    rw [hpow6]
    exact hmain
  have hb_nonneg : 0 ≤ Real.sqrt m * l ^ (-(1 / 6 : ℝ)) := by
    exact mul_nonneg (Real.sqrt_nonneg m) (Real.rpow_nonneg hl_nonneg (-(1 / 6 : ℝ)))
  exact le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hb_nonneg hgoal6

end Commons.Analysis.Real