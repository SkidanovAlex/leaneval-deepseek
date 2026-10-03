import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star

namespace Commons.Analysis.Real

theorem floor_mul_geom_ratio (s n : ℕ) (hs : 1 ≤ s) :
    (Nat.floor ((s : ℝ) * (1 + (s : ℝ)⁻¹) ^ (n + 1)) : ℝ)
      ≤ (1 + 3 / (s : ℝ)) * (Nat.floor ((s : ℝ) * (1 + (s : ℝ)⁻¹) ^ n) : ℝ) := by
  have hs_pos : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast (show (0 : ℕ) < s from lt_of_lt_of_le Nat.zero_lt_one hs)
  set r : ℝ := 1 + (s : ℝ)⁻¹ with hr
  have hr1 : 1 ≤ r := by
    rw [hr]
    have h : (0 : ℝ) ≤ (s : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hs_pos)
    linarith
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  have hpow : 1 ≤ r ^ n := one_le_pow₀ hr1
  set a : ℝ := (s : ℝ) * r ^ n with ha
  have ha_ge : (s : ℝ) ≤ a := by
    rw [ha]
    calc (s : ℝ) = (s : ℝ) * 1 := by ring
      _ ≤ (s : ℝ) * r ^ n := mul_le_mul_of_nonneg_left hpow (le_of_lt hs_pos)
  have ha_pos : 0 < a := lt_of_lt_of_le hs_pos ha_ge
  set m : ℕ := Nat.floor a with hm
  have hm_ge_s : s ≤ m := by
    rw [hm]
    exact Nat.le_floor ha_ge
  have hm_ge : ((s : ℝ) + 1) ≤ 2 * (m : ℝ) := by
    have h2 : s + 1 ≤ 2 * m := by omega
    exact_mod_cast h2
  have hkey : (1 + (s : ℝ)⁻¹) * ((m : ℝ) + 1) ≤ (1 + 3 / (s : ℝ)) * (m : ℝ) := by
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
    have e1 : (1 + (s : ℝ)⁻¹) * ((m : ℝ) + 1) * (s : ℝ) = ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
      field_simp
    have e2 : (1 + 3 / (s : ℝ)) * (m : ℝ) * (s : ℝ) = ((s : ℝ) + 3) * (m : ℝ) := by
      field_simp
    have hcore : ((s : ℝ) + 1) * ((m : ℝ) + 1) ≤ ((s : ℝ) + 3) * (m : ℝ) := by
      nlinarith [hm_ge]
    rw [← mul_le_mul_iff_of_pos_right hs_pos]
    rw [e1, e2]
    exact hcore
  have hb_eq : (s : ℝ) * r ^ (n + 1) = a * r := by
    rw [ha, pow_succ]
    ring
  have ha_lt : a < (m : ℝ) + 1 := by
    rw [hm]
    exact Nat.lt_floor_add_one a
  have hb_lt : (s : ℝ) * r ^ (n + 1) < ((m : ℝ) + 1) * r := by
    rw [hb_eq]
    exact mul_lt_mul_of_pos_right ha_lt hrpos
  have hle : ((m : ℝ) + 1) * r ≤ (1 + 3 / (s : ℝ)) * (m : ℝ) := by
    rw [hr, mul_comm ((m : ℝ) + 1) (1 + (s : ℝ)⁻¹)]
    exact hkey
  have h1 : (Nat.floor ((s : ℝ) * r ^ (n + 1)) : ℝ) ≤ (s : ℝ) * r ^ (n + 1) :=
    Nat.floor_le (le_of_lt (mul_pos hs_pos (pow_pos hrpos (n + 1))))
  exact le_of_lt (lt_of_le_of_lt h1 (lt_of_lt_of_le hb_lt hle))

end Commons.Analysis.Real