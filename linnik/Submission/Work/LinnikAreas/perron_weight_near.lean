import Mathlib

namespace Work.LinnikAreas

/-- For `0 < u ≤ 2`, the logarithm dominates the linear term: `|1 - u| ≤ 2 * |log u|`. -/
lemma log_lower_bound (u : ℝ) (h0 : 0 < u) (h2 : u ≤ 2) :
    |1 - u| ≤ 2 * |Real.log u| := by
  rcases le_or_gt 1 u with hu | hu
  · -- 1 ≤ u ≤ 2
    have hlog : (u - 1) / u ≤ Real.log u := by
      have h := Real.one_sub_inv_le_log_of_pos h0
      have h' : 1 - u⁻¹ = (u - 1) / u := by
        rw [sub_div, div_self (ne_of_gt h0), one_div]
      rwa [h'] at h
    have h1u : 1 - u ≤ 0 := by linarith
    have hlognn : 0 ≤ Real.log u := Real.log_nonneg hu
    rw [abs_of_nonpos h1u, abs_of_nonneg hlognn]
    have hstep : (u - 1) ≤ 2 * ((u - 1) / u) := by
      rw [← mul_div_assoc, le_div_iff₀ h0]
      nlinarith [hu, h2]
    linarith
  · -- 0 < u ≤ 1
    have hle1 : u ≤ 1 := le_of_lt hu
    have hlog : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos h0
    have h1u : 0 ≤ 1 - u := by linarith
    have hlognp : Real.log u ≤ 0 := Real.log_nonpos (le_of_lt h0) hle1
    rw [abs_of_nonneg h1u, abs_of_nonpos hlognp]
    linarith

/-- Core estimate: the weight `1/(T |log(x/y)|)` is bounded by `2/(x |x-y|)`,
in the regime `x ≥ 1`, `T ≥ x^2`, `0 ≤ y ≤ 2x`. -/
lemma perron_core {x T y : ℝ} (hx : 1 ≤ x) (hT : x ^ 2 ≤ T) (hy0 : 0 ≤ y)
    (hy : y ≤ 2 * x) :
    1 / (T * |Real.log (x / y)|) ≤ 2 / (x * |x - y|) := by
  have hxpos : 0 < x := by linarith
  have hx2pos : 0 < x ^ 2 := pow_pos hxpos 2
  rcases lt_or_eq_of_le hy0 with hypos | hyzero
  · -- 0 < y
    by_cases hxy : x = y
    · -- x = y : both sides vanish
      rw [hxy]
      simp [div_self (ne_of_gt hypos)]
    · -- x ≠ y
      have hyx_pos : 0 < y / x := div_pos hypos hxpos
      have hyx_le : y / x ≤ 2 := by
        rw [div_le_iff₀ hxpos]
        linarith [hy]
      have hlogb : |1 - y / x| ≤ 2 * |Real.log (y / x)| :=
        log_lower_bound (y / x) hyx_pos hyx_le
      have hlog_eq : Real.log (y / x) = -Real.log (x / y) := by
        rw [Real.log_div (ne_of_gt hypos) (ne_of_gt hxpos),
          Real.log_div (ne_of_gt hxpos) (ne_of_gt hypos)]
        ring
      have e1 : x * |1 - y / x| = |x - y| := by
        nth_rewrite 1 [← abs_of_pos hxpos]
        rw [← abs_mul]
        congr 1
        field_simp
      have hDle : |x - y| ≤ 2 * x * |Real.log (x / y)| := by
        calc |x - y| = x * |1 - y / x| := e1.symm
          _ ≤ x * (2 * |Real.log (y / x)|) :=
              mul_le_mul_of_nonneg_left hlogb (le_of_lt hxpos)
          _ = 2 * x * |Real.log (x / y)| := by rw [hlog_eq, abs_neg]; ring
      have hxD : x * |x - y| ≤ 2 * (T * |Real.log (x / y)|) := by
        have hLnn : 0 ≤ |Real.log (x / y)| := abs_nonneg _
        calc x * |x - y| ≤ x * (2 * x * |Real.log (x / y)|) :=
              mul_le_mul_of_nonneg_left hDle (le_of_lt hxpos)
          _ = 2 * x ^ 2 * |Real.log (x / y)| := by ring
          _ ≤ 2 * T * |Real.log (x / y)| := by
              apply mul_le_mul_of_nonneg_right _ hLnn
              linarith [hT]
          _ = 2 * (T * |Real.log (x / y)|) := by ring
      have hxDpos : 0 < x * |x - y| := by
        apply mul_pos hxpos
        rw [abs_pos]
        exact sub_ne_zero.mpr hxy
      have hTLpos : 0 < T * |Real.log (x / y)| := by
        have h2 : (0 : ℝ) < 2 * (T * |Real.log (x / y)|) := lt_of_lt_of_le hxDpos hxD
        linarith
      rw [div_le_div_iff₀ hTLpos hxDpos]
      simpa using hxD
  · -- y = 0 : left side vanishes
    rw [← hyzero]
    simp only [div_zero, Real.log_zero, abs_zero, mul_zero, sub_zero]
    apply div_nonneg (by norm_num)
    exact mul_nonneg (le_of_lt hxpos) (abs_nonneg x)

theorem perron_weight_near :
    ∀ x T : ℝ, ∀ n : ℕ, 1 ≤ x → x ^ 2 ≤ T → (n : ℝ) ≤ 2 * x →
      min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
        ≤ 2 / x ^ 2 + min 1 (3 / (x * |x - (n : ℝ)|)) := by
  intro x T n hx hT hn
  have hxpos : 0 < x := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcore : 1 / (T * |Real.log (x / (n : ℝ))|) ≤ 2 / (x * |x - (n : ℝ)|) :=
    perron_core hx hT hn0 hn
  rcases le_or_gt 1 (3 / (x * |x - (n : ℝ)|)) with hB | hB
  · rw [min_eq_left hB]
    have h1 : min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) ≤ 1 := min_le_left _ _
    have h2 : (0 : ℝ) ≤ 2 / x ^ 2 := div_nonneg (by norm_num) (sq_nonneg x)
    linarith
  · rw [min_eq_right (le_of_lt hB)]
    calc min 1 (1 / (T * |Real.log (x / (n : ℝ))|))
        ≤ 1 / (T * |Real.log (x / (n : ℝ))|) := min_le_right _ _
      _ ≤ 2 / (x * |x - (n : ℝ)|) := hcore
      _ ≤ 2 / x ^ 2 + 3 / (x * |x - (n : ℝ)|) := by
          have hle1 : 2 / (x * |x - (n : ℝ)|) ≤ 3 / (x * |x - (n : ℝ)|) :=
            div_le_div_of_nonneg_right (by norm_num)
              (mul_nonneg (le_of_lt hxpos) (abs_nonneg _))
          have hle2 : (0 : ℝ) ≤ 2 / x ^ 2 := div_nonneg (by norm_num) (sq_nonneg x)
          linarith

end Work.LinnikAreas
