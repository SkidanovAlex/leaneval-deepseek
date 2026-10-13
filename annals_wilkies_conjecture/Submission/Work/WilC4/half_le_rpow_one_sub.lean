import Mathlib

namespace Work.WilC4

lemma half_le_rpow_one_sub (u n : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (hn : 0 ≤ n)
    (hnu : n * u ≤ Real.log 2 / 2) : (1 - u) ^ n ≥ 1 / 2 := by
  have hpos : 0 < 1 - u := by linarith
  -- `(1 - u)⁻¹ ≤ 2` because `u ≤ 1/2`.
  have h2 : (1 - u)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  -- `1 - x⁻¹ = -u x⁻¹` for `x = 1 - u`.
  have hid : 1 - (1 - u)⁻¹ = -u * (1 - u)⁻¹ := by
    have hne : (1 - u) ≠ 0 := ne_of_gt hpos
    field_simp
    ring
  -- The standard inequality `1 - x⁻¹ ≤ log x` at `x = 1 - u`.
  have hlog_lower : -u * (1 - u)⁻¹ ≤ Real.log (1 - u) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    simpa only [hid] using h
  have hlog2_0 : 0 ≤ Real.log 2 / 2 := by
    have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  -- `(n u) (1 - u)⁻¹ ≤ log 2` from `n u ≤ log 2 / 2` and `(1 - u)⁻¹ ≤ 2`.
  have hprod : (n * u) * (1 - u)⁻¹ ≤ Real.log 2 := by
    calc (n * u) * (1 - u)⁻¹ ≤ (Real.log 2 / 2) * 2 :=
          mul_le_mul hnu h2 (inv_nonneg.mpr hpos.le) hlog2_0
      _ = Real.log 2 := by ring
  have h1 : (-u * (1 - u)⁻¹) * n ≤ Real.log (1 - u) * n :=
    mul_le_mul_of_nonneg_right hlog_lower hn
  have h2' : -(Real.log 2) ≤ (-u * (1 - u)⁻¹) * n := by
    have hneg := neg_le_neg hprod
    have heq : (-u * (1 - u)⁻¹) * n = -((n * u) * (1 - u)⁻¹) := by ring
    rw [heq]
    exact hneg
  -- Hence `log (1/2) ≤ n * log (1 - u)`.
  have hkey : Real.log (1 / 2) ≤ Real.log (1 - u) * n := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
    exact le_trans h2' h1
  rw [ge_iff_le, Real.rpow_def_of_pos hpos]
  rw [show (1 / 2 : ℝ) = Real.exp (Real.log (1 / 2)) from
        (Real.exp_log (by norm_num)).symm]
  exact Real.exp_le_exp.mpr hkey

end Work.WilC4
