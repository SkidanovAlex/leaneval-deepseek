import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

theorem rauch_B_mid {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (h121 : 1 / 121 ≤ c) :
    6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c) ≤ 12 * c := by
  -- Arithmetic core.  Writing `L = log (4/√c)` and `M = log (8/c)`, the hypotheses give
  --   `ε₁ < c/(4π)`,  `L ≤ 4` (since `4/√c ≤ 44 < e⁴`),  `0 ≤ L` (since `c ≤ 1/4`),
  --   `M ≤ 7` (since `8/c ≤ 968 < e⁷`).
  -- Hence `6ε₁(1+L²) < 6(c/(4π))(17) = 25.5 c/π < 8.5 c` (as `π > 3`), while
  -- `3c/2 + (c/4)M ≤ 1.5c + 1.75c`; total `< 11.75 c ≤ 12 c`.
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  -- `ε₁ < c/(4π)`
  have hε : ε₁ < c / (4 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hnum2]
  have hspos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  -- `√c ≥ 1/11`, hence `4/√c ≤ 44`
  have h11 : (1:ℝ)/11 ≤ Real.sqrt c := by
    have h := Real.sqrt_le_sqrt h121
    have h1 : Real.sqrt (1/121 : ℝ) = 1/11 := by
      rw [show (1/121:ℝ) = (1/11)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h1] at h
  have h44 : 4 / Real.sqrt c ≤ 44 := by
    rw [div_le_iff₀ hspos]
    nlinarith [h11]
  -- numerical exponential bounds `44 ≤ e⁴` and `968 ≤ e⁷` (via `e > 2.7`)
  have hexp44 : (44:ℝ) ≤ Real.exp 4 := by
    have h27 : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : (2.7:ℝ)^4 < (Real.exp 1)^4 := pow_lt_pow_left₀ h27 (by norm_num) (by norm_num)
    have he : Real.exp (4:ℝ) = (Real.exp 1)^4 := by
      rw [show (4:ℝ) = (4:ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [he]
    nlinarith [hpow]
  have hexp968 : (968:ℝ) ≤ Real.exp 7 := by
    have h27 : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : (2.7:ℝ)^7 < (Real.exp 1)^7 := pow_lt_pow_left₀ h27 (by norm_num) (by norm_num)
    have he : Real.exp (7:ℝ) = (Real.exp 1)^7 := by
      rw [show (7:ℝ) = (7:ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [he]
    nlinarith [hpow]
  -- `L ≤ 4`
  have hL4 : Real.log (4 / Real.sqrt c) ≤ 4 := by
    have hpos : 0 < 4 / Real.sqrt c := by positivity
    have h := Real.log_le_log hpos (le_trans h44 hexp44)
    rwa [Real.log_exp] at h
  -- `0 ≤ L`
  have hL0 : 0 ≤ Real.log (4 / Real.sqrt c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hspos]
    have hsl : Real.sqrt c ≤ 1/2 := by
      have h := Real.sqrt_le_sqrt hc1
      have h1 : Real.sqrt (1/4 : ℝ) = 1/2 := by
        rw [show (1/4:ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h1] at h
    nlinarith [hsl]
  -- `1 + L² ≤ 17`
  have hL2 : (Real.log (4 / Real.sqrt c))^2 ≤ 16 := by
    have h := pow_le_pow_left₀ hL0 hL4 2
    norm_num at h
    exact h
  -- `M ≤ 7`
  have h8c : 8 / c ≤ 968 := by
    rw [div_le_iff₀ hc]
    nlinarith [h121]
  have hlog8 : Real.log (8 / c) ≤ 7 := by
    have hpos : 0 < 8 / c := by positivity
    have h := Real.log_le_log hpos (le_trans h8c hexp968)
    rwa [Real.log_exp] at h
  -- assembly
  have h1 : ε₁ * (1 + (Real.log (4 / Real.sqrt c))^2) ≤ (c / (4 * Real.pi)) * 17 :=
    mul_le_mul (le_of_lt hε) (by nlinarith [hL2]) (by positivity) (by positivity)
  have h2 : 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c))^2) + c / 4)
      ≤ 6 * ((c / (4 * Real.pi)) * 17 + c / 4) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith [h1]
  have h3 : (c / 4) * Real.log (8 / c) ≤ (c / 4) * 7 :=
    mul_le_mul_of_nonneg_left hlog8 (by positivity)
  have hdiv : 6 * ((c / (4 * Real.pi)) * 17) ≤ 8.5 * c := by
    have h4pi : (0:ℝ) < 4 * Real.pi := by positivity
    rw [show 6 * (c / (4 * Real.pi) * 17) = 102 * c / (4 * Real.pi) by ring]
    rw [div_le_iff₀ h4pi]
    have h := mul_lt_mul_of_pos_right hpi3 (show (0:ℝ) < 34 * c by positivity)
    nlinarith [h]
  nlinarith [h2, h3, hdiv, hc]

end Work.Diff.C.geoCrux
