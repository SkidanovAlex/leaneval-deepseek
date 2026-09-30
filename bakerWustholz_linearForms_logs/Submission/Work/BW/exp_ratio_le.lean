import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `2 e^{h+2}(r-1)/4^h ≤ 1.175 h r` for `h ≥ 19`, `r ≥ 2`. -/
theorem exp_ratio_le {h r : ℕ} (hh : 19 ≤ h) (hr : 2 ≤ r) :
    2 * Real.exp ((h : ℝ) + 2) * ((r : ℝ) - 1) / (4 : ℝ) ^ h
      ≤ 1.175 * (h : ℝ) * (r : ℝ) := by
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have h4pos : (0:ℝ) < (4:ℝ)^h := by positivity
  have hr1nn : (0:ℝ) ≤ (r:ℝ) - 1 := by linarith
  have hexp : Real.exp ((h:ℝ) + 2) ≤ (3:ℝ)^(h+2) := by
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h2 : Real.exp 2 < 9 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1, h1]
    have hp : Real.exp (h:ℝ) = (Real.exp 1)^h := by
      rw [show (h:ℝ) = (h:ℝ) * 1 by ring]
      exact Real.exp_nat_mul 1 h
    rw [Real.exp_add, hp]
    calc (Real.exp 1)^h * Real.exp 2 ≤ (3:ℝ)^h * 9 := by gcongr
      _ = (3:ℝ)^(h+2) := by rw [pow_add]; norm_num
  have key : 2 * (3:ℝ)^(h+2) ≤ 18 * (4:ℝ)^h := by
    have h34 : (3:ℝ)^h ≤ (4:ℝ)^h := by gcongr; norm_num
    have e1 : 2 * (3:ℝ)^(h+2) = 18 * (3:ℝ)^h := by rw [pow_add]; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left h34 (by norm_num)
  have hstep2 : 2 * (3:ℝ)^(h+2) * ((r:ℝ)) / (4:ℝ)^h ≤ 18 * (r:ℝ) := by
    rw [div_le_iff₀ h4pos]
    have hmul := mul_le_mul_of_nonneg_right key (le_of_lt hr0)
    calc 2 * (3:ℝ)^(h+2) * (r:ℝ) = (2 * (3:ℝ)^(h+2)) * (r:ℝ) := rfl
      _ ≤ (18 * (4:ℝ)^h) * (r:ℝ) := hmul
      _ = 18 * (r:ℝ) * (4:ℝ)^h := by ring
  have hfin : 18 * (r:ℝ) ≤ 1.175 * (h:ℝ) * (r:ℝ) := by
    have hh' : (18:ℝ) ≤ 1.175 * (h:ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right hh' (le_of_lt hr0)
  calc 2 * Real.exp ((h:ℝ)+2) * ((r:ℝ)-1) / (4:ℝ)^h
      ≤ 2 * (3:ℝ)^(h+2) * ((r:ℝ)-1) / (4:ℝ)^h := by
        apply div_le_div_of_nonneg_right _ (le_of_lt h4pos)
        exact mul_le_mul_of_nonneg_right (by linarith [hexp]) hr1nn
    _ ≤ 2 * (3:ℝ)^(h+2) * (r:ℝ) / (4:ℝ)^h := by
        apply div_le_div_of_nonneg_right _ (le_of_lt h4pos)
        exact mul_le_mul_of_nonneg_left (by linarith : (r:ℝ)-1 ≤ (r:ℝ)) (by positivity)
    _ ≤ 18 * (r:ℝ) := hstep2
    _ ≤ 1.175 * (h:ℝ) * (r:ℝ) := hfin

end Work.BW
