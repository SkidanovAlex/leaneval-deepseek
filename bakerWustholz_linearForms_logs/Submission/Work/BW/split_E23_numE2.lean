import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem split_E23_numE2 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (2:ℝ)^(7*r+7) * (r:ℝ)^(2*r+2) < (2:ℝ)^3 * (11:ℝ)^r * (2*(r:ℝ)*d)^(6*r) := by
  have hR2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hD1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  -- Key numeric inequality: 2^(r+4) < 11^r * r^(4r-2)
  have hle : r + 4 ≤ 4*r - 2 := by omega
  have h1 : (2:ℝ)^(r+4) ≤ (2:ℝ)^(4*r-2) := pow_le_pow_right₀ (by norm_num) hle
  have h2 : (2:ℝ)^(4*r-2) ≤ (r:ℝ)^(4*r-2) := pow_le_pow_left₀ (by norm_num) hR2 _
  have h3 : (121:ℝ) ≤ (11:ℝ)^r := by
    calc (121:ℝ) = (11:ℝ)^2 := by norm_num
      _ ≤ (11:ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
  have hpowpos : (0:ℝ) < (2:ℝ)^(4*r-2) := by positivity
  have h35 : (2:ℝ)^(r+4) < 121 * (2:ℝ)^(4*r-2) := by nlinarith [h1, hpowpos]
  have hprod : (121:ℝ) * (2:ℝ)^(4*r-2) ≤ (11:ℝ)^r * (r:ℝ)^(4*r-2) :=
    mul_le_mul h3 h2 (by positivity) (by positivity)
  have key : (2:ℝ)^(r+4) < (11:ℝ)^r * (r:ℝ)^(4*r-2) := lt_of_lt_of_le h35 hprod
  -- Multiply the key inequality by the positive factor P = 2^(6r+3) * r^(2r+2)
  have hP : (0:ℝ) < (2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+2) := by positivity
  have hmul : (2:ℝ)^(r+4) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+2))
      < ((11:ℝ)^r * (r:ℝ)^(4*r-2)) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+2)) :=
    mul_lt_mul_of_pos_right key hP
  have hh : (2:ℝ)^(r+4) * (2:ℝ)^(6*r+3) = (2:ℝ)^(7*r+7) := by
    rw [← pow_add]; congr 1; omega
  have e1 : (2:ℝ)^(r+4) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+2))
      = (2:ℝ)^(7*r+7) * (r:ℝ)^(2*r+2) := by
    rw [← hh, mul_assoc]
  have hr6 : (r:ℝ)^(6*r) = (r:ℝ)^(4*r-2) * (r:ℝ)^(2*r+2) := by
    rw [← pow_add]; congr 1; omega
  have h2c : (2:ℝ)^(6*r+3) = (2:ℝ)^3 * (2:ℝ)^(6*r) := by
    rw [← pow_add]; congr 1; omega
  have e2 : ((11:ℝ)^r * (r:ℝ)^(4*r-2)) * ((2:ℝ)^(6*r+3) * (r:ℝ)^(2*r+2))
      = (2:ℝ)^3 * (11:ℝ)^r * (2*(r:ℝ))^(6*r) := by
    rw [mul_pow, hr6, h2c]; ring
  rw [e1, e2] at hmul
  -- Bound (2r)^(6r) ≤ (2rd)^(6r) using d ≥ 1
  have hfinal : (2:ℝ)^3 * (11:ℝ)^r * (2*(r:ℝ))^(6*r)
      ≤ (2:ℝ)^3 * (11:ℝ)^r * (2*(r:ℝ)*d)^(6*r) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [hD1, hR2]
  linarith

end Work.BW
