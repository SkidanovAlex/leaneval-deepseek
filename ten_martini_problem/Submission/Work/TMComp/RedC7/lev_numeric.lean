import Mathlib

/-!
# `RedC7.app_numeric`: the numerical step for the large deviation theorem

In `large_deviation` the arithmetic estimate `RedC7.arith_slack`

`Σ_{k ≤ K}(1/k)(1 + (s q ‖kα‖)²)⁻¹ ≤ 50/s² + 2/q + 12 (1/q)(1 + log (1 + K/q))`

has to be below `κ/16` (so that, multiplied by the factor `4` of the Fejér-sum bound, it is
below `κ/4`).  This holds because in `large_deviation` the parameters satisfy

`10⁴ ≤ s²κ`,  `κ ≤ 1`,  `864 ≤ Cv ≤ q κ²`,  `K < 8 e^{κq/1000}/κ² + 1`.
-/

namespace Work.TMComp.RedC7

/-- **The numerical step.** -/
theorem app_numeric (s q κ Cv : ℝ) (K : ℕ) (hk2 : 10000 ≤ s ^ 2 * κ) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hq : 0 < q) (hCv : 864 ≤ Cv) (hCvq : Cv ≤ q * κ ^ 2)
    (hKle : (K : ℝ) < 8 * Real.exp (κ * q / 1000) / κ ^ 2 + 1) :
    4 * (50 / s ^ 2 + 2 / q + 12 * (1 / q) * (1 + Real.log (1 + (K : ℝ) / q))) ≤ κ / 4 := by
  have hs2 : (0 : ℝ) < s ^ 2 := by nlinarith
  have hq864 : 864 ≤ q * κ ^ 2 := le_trans hCv hCvq
  have hκ2le : κ ^ 2 ≤ κ := by nlinarith
  have hκ2pos : (0 : ℝ) < κ ^ 2 := by positivity
  have hqinv : 1 / q ≤ κ ^ 2 / 864 := by
    rw [div_le_div_iff₀ hq (by norm_num)]
    nlinarith
  -- the first term
  have hA : 50 / s ^ 2 ≤ κ / 200 := by
    rw [div_le_div_iff₀ hs2 (by norm_num)]
    nlinarith [hk2]
  -- the second term
  have hB : 1 / q ≤ κ ^ 2 / 864 := hqinv
  -- the third term
  have hexp : (0 : ℝ) < Real.exp (κ * q / 1000) := Real.exp_pos _
  have he1 : (1 : ℝ) ≤ Real.exp (κ * q / 1000) := Real.one_le_exp (by positivity)
  have hKq : (K : ℝ) / q ≤ Real.exp (κ * q / 1000) / 108 + 1 / 864 := by
    have hA1 : (K : ℝ) / q < (8 * Real.exp (κ * q / 1000) / κ ^ 2 + 1) / q :=
      div_lt_div_of_pos_right hKle hq
    have hB1 : (8 * Real.exp (κ * q / 1000) / κ ^ 2 + 1) / q
        = 8 * Real.exp (κ * q / 1000) / (κ ^ 2 * q) + 1 / q := by
      field_simp
    have hC1 : 8 * Real.exp (κ * q / 1000) / (κ ^ 2 * q) ≤ Real.exp (κ * q / 1000) / 108 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h864 : (864 : ℝ) ≤ κ ^ 2 * q := by
        rw [mul_comm]; exact hq864
      nlinarith [hexp, h864]
    have hD1 : 1 / q ≤ 1 / 864 := by
      have hqge : (864 : ℝ) ≤ q := by nlinarith [hq864, hκ1, hq]
      rw [div_le_div_iff₀ hq (by norm_num)]
      linarith
    linarith [hA1, hB1, hC1, hD1]
  have h1p : 1 + (K : ℝ) / q ≤ (97 / 96 : ℝ) * Real.exp (κ * q / 1000) := by
    have h1 : (1 : ℝ) / 108 + 1 / 864 = 1 / 96 := by norm_num
    have h2 : Real.exp (κ * q / 1000) * (1 / 96) = Real.exp (κ * q / 1000) / 96 := by ring
    have h3 : (1 : ℝ) ≤ Real.exp (κ * q / 1000) := he1
    have h4 : (1 : ℝ) / 864 ≤ Real.exp (κ * q / 1000) * (1 / 96) := by
      have : (1 : ℝ) / 864 ≤ 1 / 96 := by norm_num
      have := mul_le_mul_of_nonneg_right he1 (show (0:ℝ) ≤ 1/96 by norm_num)
      linarith
    linarith [hKq, h1, h2, h3, h4]
  have hlog : Real.log (1 + (K : ℝ) / q) ≤ 1 / 96 + κ * q / 1000 := by
    have hpos : 0 < 1 + (K : ℝ) / q := by positivity
    have h97 : 0 < (97 / 96 : ℝ) := by norm_num
    have hlog97 : Real.log (97 / 96 : ℝ) ≤ 1 / 96 := by
      have := Real.log_le_sub_one_of_pos h97
      linarith
    calc Real.log (1 + (K : ℝ) / q)
        ≤ Real.log ((97 / 96 : ℝ) * Real.exp (κ * q / 1000)) := Real.log_le_log hpos h1p
      _ = Real.log (97 / 96 : ℝ) + κ * q / 1000 := by
          rw [Real.log_mul (ne_of_gt h97) (ne_of_gt hexp), Real.log_exp]
      _ ≤ 1 / 96 + κ * q / 1000 := by linarith
  have h3 : 12 * (1 / q) * (1 + Real.log (1 + (K : ℝ) / q))
      ≤ 12 * (1 / q) * (1 + (1 / 96 + κ * q / 1000)) := by
    have hlog' : 1 + Real.log (1 + (K : ℝ) / q) ≤ 1 + (1 / 96 + κ * q / 1000) := by linarith
    exact mul_le_mul_of_nonneg_left hlog' (by positivity)
  have h3' : (1 / q) * (1 + (1 / 96 + κ * q / 1000)) ≤ (97 / 96) * (κ ^ 2 / 864) + κ / 1000 := by
    have h1 : (1 / q) * (1 + (1 / 96 + κ * q / 1000))
        = (97 / 96) * (1 / q) + κ / 1000 := by
      field_simp
      ring
    rw [h1]
    have h2 : (97 / 96) * (1 / q) ≤ (97 / 96) * (κ ^ 2 / 864) :=
      mul_le_mul_of_nonneg_left hqinv (by norm_num)
    linarith
  -- assemble
  have hsum : 50 / s ^ 2 + 2 / q + 12 * (1 / q) * (1 + Real.log (1 + (K : ℝ) / q))
      ≤ κ / 200 + 2 * (κ ^ 2 / 864) + 12 * ((97 / 96) * (κ ^ 2 / 864) + κ / 1000) := by
    have h2 : 2 / q ≤ 2 * (κ ^ 2 / 864) := by
      have h := mul_le_mul_of_nonneg_left hqinv (show (0 : ℝ) ≤ 2 by norm_num)
      have heq : (2 : ℝ) / q = 2 * (1 / q) := by ring
      linarith [h, heq]
    have h4 : 12 * (1 / q) * (1 + Real.log (1 + (K : ℝ) / q))
        ≤ 12 * ((97 / 96) * (κ ^ 2 / 864) + κ / 1000) := by
      have h := mul_le_mul_of_nonneg_left h3' (show (0 : ℝ) ≤ 12 by norm_num)
      have heq : (12 : ℝ) * ((1 / q) * (1 + (1 / 96 + κ * q / 1000)))
          = 12 * (1 / q) * (1 + (1 / 96 + κ * q / 1000)) := by ring
      linarith [h, h3, heq]
    linarith [hA, h2, h4]
  have h4 : 4 * (κ / 200 + 2 * (κ ^ 2 / 864) + 12 * ((97 / 96) * (κ ^ 2 / 864) + κ / 1000))
      ≤ κ / 4 := by
    nlinarith [hκ2le, hκ0]
  have h5 : 4 * (50 / s ^ 2 + 2 / q + 12 * (1 / q) * (1 + Real.log (1 + (K : ℝ) / q)))
      ≤ 4 * (κ / 200 + 2 * (κ ^ 2 / 864)
          + 12 * ((97 / 96) * (κ ^ 2 / 864) + κ / 1000)) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  linarith [h5, h4]

end Work.TMComp.RedC7
