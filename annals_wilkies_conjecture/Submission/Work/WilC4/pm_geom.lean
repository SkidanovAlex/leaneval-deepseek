import Mathlib

namespace Work.WilC4

theorem pm_geom {a b r : ℝ} {m : ℕ} (ha : 0 < a) (hab : a < b) (hm : 0 < m)
    (hr : r = (b / a) ^ ((1 : ℝ) / (m : ℝ))) :
    1 < r ∧ a * r ^ m = b ∧ (∀ i ≤ m, a ≤ a * r ^ i ∧ a * r ^ i ≤ b) ∧
      (∀ i, a * r ^ i < a * r ^ (i + 1)) := by
  have han : a ≠ 0 := ne_of_gt ha
  have hmr : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmr
  have hba : 1 < b / a := (one_lt_div ha).mpr hab
  have hbapos : 0 < b / a := lt_trans zero_lt_one hba
  have h1m : 0 < (1 : ℝ) / (m : ℝ) := div_pos one_pos hmr
  have hr1 : 1 < r := by rw [hr]; exact Real.one_lt_rpow hba h1m
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have hrge : 1 ≤ r := le_of_lt hr1
  have hrm : r ^ m = b / a := by
    rw [hr, ← Real.rpow_natCast ((b / a) ^ ((1 : ℝ) / (m : ℝ))) m,
      ← Real.rpow_mul (le_of_lt hbapos) ((1 : ℝ) / (m : ℝ)) (m : ℝ),
      one_div_mul_cancel hmne, Real.rpow_one]
  have hamul : a * (b / a) = b := by
    rw [mul_comm, div_mul_cancel₀ b han]
  refine ⟨hr1, ?_, ?_, ?_⟩
  · rw [hrm, hamul]
  · intro i hi
    exact ⟨le_mul_of_one_le_right ha.le (one_le_pow₀ hrge),
      calc a * r ^ i ≤ a * r ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrge hi) ha.le
        _ = b := by rw [hrm, hamul]⟩
  · intro i
    have hstep : r ^ i < r ^ (i + 1) := by
      rw [pow_succ]
      exact lt_mul_of_one_lt_right (pow_pos hrpos i) hr1
    exact mul_lt_mul_of_pos_left hstep ha

end Work.WilC4
