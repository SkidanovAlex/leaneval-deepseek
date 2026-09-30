import Mathlib
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Elementary bounds on `pxi r = 1 - 0.536/r` used by `Work.BW.split_E23`. -/

namespace Work.BW

theorem pxi_nonneg (r : ℕ) : 0 ≤ pxi r := by
  rcases Nat.eq_zero_or_pos r with h | h
  · simp [pxi, h]
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h
    have h1 : (0.536 : ℝ) / r ≤ 0.536 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < r)]
      nlinarith
    simp only [pxi]; linarith

/-- `1.05 ≤ 2 ξ^r` for `r ≥ 2`. -/
theorem one05_le_two_mul_pxi_pow {r : ℕ} (hr : 2 ≤ r) : (1.05 : ℝ) ≤ 2 * (pxi r) ^ r := by
  rcases lt_or_ge r 21 with h | h
  · interval_cases r <;> norm_num [pxi]
  · have h21 : (21 : ℝ) ≤ r := by exact_mod_cast h
    have hr' : (0 : ℝ) < r := by linarith
    have hy : (0.536 : ℝ) / r < 1 := by rw [div_lt_one hr']; linarith
    have hpos1 : (0 : ℝ) < 1 - 0.536 / r := by linarith
    have ha : (0.536 : ℝ) / r ≤ 0.536 / 21 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h21
    have ha1 : ((0.536 : ℝ) / r) ≠ 1 := ne_of_lt hy
    have hA : -Real.log (1 - (0.536 : ℝ) / r) ≤ (0.536 : ℝ) / r * (1 - (0.536 : ℝ) / r)⁻¹ := by
      have h1 : -Real.log (1 - (0.536 : ℝ) / r) = Real.log ((1 - (0.536 : ℝ) / r)⁻¹) := by
        rw [Real.log_inv]
      rw [h1]
      have h2 : Real.log ((1 - (0.536 : ℝ) / r)⁻¹) ≤ (1 - (0.536 : ℝ) / r)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr hpos1)
      have h3 := inv_one_sub_sub_one ha1
      linarith
    have hkey : (r : ℝ) * (-Real.log (pxi r)) ≤ 0.64 := by
      have hxir : pxi r = 1 - 0.536 / r := rfl
      rw [hxir]
      have hmul : (r : ℝ) * (-Real.log (1 - (0.536 : ℝ) / r))
          ≤ (r : ℝ) * ((0.536 : ℝ) / r * (1 - (0.536 : ℝ) / r)⁻¹) :=
        mul_le_mul_of_nonneg_left hA (le_of_lt hr')
      have hsimp : (r : ℝ) * ((0.536 : ℝ) / r * (1 - (0.536 : ℝ) / r)⁻¹)
          = 0.536 * (1 - (0.536 : ℝ) / r)⁻¹ := by
        field_simp
      have hlast : 0.536 * (1 - (0.536 : ℝ) / r)⁻¹ ≤ 0.64 := by
        rw [inv_eq_one_div, ← div_eq_mul_one_div]
        rw [div_le_iff₀ hpos1]
        nlinarith [ha]
      linarith
    have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog105 : Real.log (1.05 : ℝ) ≤ 0.05 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.05 by norm_num)
      linarith
    have hlt : (0 : ℝ) < 2 * (pxi r) ^ r := by
      have := pxi_pos hr
      positivity
    have hpos105 : (0 : ℝ) < 1.05 := by norm_num
    have hloggoalle : Real.log (1.05 : ℝ) ≤ Real.log (2 * (pxi r) ^ r) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos (pxi_pos hr) r)), Real.log_pow]
      nlinarith
    exact (Real.log_le_log_iff hpos105 hlt).mp hloggoalle

theorem half_le_pxi_pow {r : ℕ} (hr : 2 ≤ r) : (1 / 2 : ℝ) ≤ (pxi r) ^ r := by
  have := one05_le_two_mul_pxi_pow hr; linarith

theorem one_le_two_mul_pxi_pow {r : ℕ} (hr : 2 ≤ r) : (1 : ℝ) ≤ 2 * (pxi r) ^ r := by
  have := one05_le_two_mul_pxi_pow hr; linarith

theorem pxi_pow_pos {r : ℕ} (hr : 2 ≤ r) : (0 : ℝ) < (pxi r) ^ r := pow_pos (pxi_pos hr) r

theorem pxi_pow_le_one (r : ℕ) : (pxi r) ^ r ≤ 1 :=
  pow_le_one₀ (pxi_nonneg r) (pxi_le_one r)

theorem pxi_pow_pred_nonneg (r : ℕ) : 0 ≤ (pxi r) ^ (r - 1) := pow_nonneg (pxi_nonneg r) _

theorem half_le_pxi_pow_pred {r : ℕ} (hr : 2 ≤ r) : (1 / 2 : ℝ) ≤ (pxi r) ^ (r - 1) := by
  have h1 : (pxi r) ^ r ≤ (pxi r) ^ (r - 1) :=
    pow_le_pow_of_le_one (pxi_nonneg r) (pxi_le_one r) (Nat.sub_le r 1)
  linarith [half_le_pxi_pow hr]

theorem one_le_two_mul_pxi_pow_pred {r : ℕ} (hr : 2 ≤ r) : (1 : ℝ) ≤ 2 * (pxi r) ^ (r - 1) := by
  have := half_le_pxi_pow_pred hr; linarith

theorem pxi_pow_pred_le_one (r : ℕ) : (pxi r) ^ (r - 1) ≤ 1 :=
  pow_le_one₀ (pxi_nonneg r) (pxi_le_one r)

theorem one_le_two_mul_pxi_pow_pred2 {r : ℕ} (hr : 2 ≤ r) : (1 : ℝ) ≤ 2 * (pxi r) ^ (r - 2) := by
  have h1 : (pxi r) ^ (r - 1) ≤ (pxi r) ^ (r - 2) :=
    pow_le_pow_of_le_one (pxi_nonneg r) (pxi_le_one r) (by omega)
  linarith [half_le_pxi_pow_pred hr]

end Work.BW
