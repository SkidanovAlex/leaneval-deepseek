import Mathlib
import Submission.Work.CNum.Hfun_defs

namespace Work.CNum

/-- In `eterm m φ = 1 + 2 r^m cos(mφ) + (r^m)²`, the "inside" is bounded below by `(1 - r^m)²`
(the minimum over the angle is attained at `cos = -1`). -/
lemma eterm_lower (m : ℕ) (φ : ℝ) : (1 - r34 ^ m) ^ 2 ≤ eterm m φ := by
  have hu_pos : 0 < r34 ^ m := r34_pow_pos m
  have hcos_ge : -1 ≤ Real.cos ((m : ℝ) * φ) := Real.neg_one_le_cos _
  rw [eterm]
  nlinarith [hcos_ge, hu_pos]

/-- The second-derivative numerator is dominated by the denominator:
`|cos(mφ)(1 + (r^m)²) + 2 r^m| ≤ eterm m φ`. -/
lemma cterm_num_bound (m : ℕ) (φ : ℝ) :
    |Real.cos ((m : ℝ) * φ) * (1 + (r34 ^ m) ^ 2) + 2 * r34 ^ m| ≤ eterm m φ := by
  have hu_pos : 0 < r34 ^ m := r34_pow_pos m
  have hcos_ge : -1 ≤ Real.cos ((m : ℝ) * φ) := Real.neg_one_le_cos _
  have hcos_le : Real.cos ((m : ℝ) * φ) ≤ 1 := Real.cos_le_one _
  rw [abs_le, eterm]
  constructor <;>
    nlinarith [hcos_ge, hcos_le, hu_pos, sq_nonneg (1 - r34 ^ m), sq_nonneg (1 + r34 ^ m)]

theorem cterm_bounds (m : ℕ) (hm : 1 ≤ m) (φ : ℝ) :
    |ctermDeriv m φ| ≤ 24 * (m : ℝ) * r34 ^ m / (1 - r34 ^ m) ^ 2 ∧
    |ctermDeriv2 m φ| ≤ 24 * (m : ℝ) ^ 2 * r34 ^ m / (1 - r34 ^ m) ^ 2 := by
  have hu_pos : 0 < r34 ^ m := r34_pow_pos m
  have hu_lt : r34 ^ m < 1 := r34_pow_lt_one hm
  have h1mu_pos : 0 < 1 - r34 ^ m := by linarith
  have hd_pos : 0 < (1 - r34 ^ m) ^ 2 := pow_pos h1mu_pos 2
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hu0 : (0 : ℝ) ≤ r34 ^ m := le_of_lt hu_pos
  have hcos_ge : -1 ≤ Real.cos ((m : ℝ) * φ) := Real.neg_one_le_cos _
  have hsin_le : |Real.sin ((m : ℝ) * φ)| ≤ 1 := Real.abs_sin_le_one _
  have hE_lb : (1 - r34 ^ m) ^ 2 ≤ eterm m φ := eterm_lower m φ
  have hE_pos : 0 < eterm m φ := lt_of_lt_of_le hd_pos hE_lb
  have hnum : |Real.cos ((m : ℝ) * φ) * (1 + (r34 ^ m) ^ 2) + 2 * r34 ^ m| ≤ eterm m φ :=
    cterm_num_bound m φ
  have hc1nn : 0 ≤ 24 * (m : ℝ) * r34 ^ m := mul_nonneg (mul_nonneg (by norm_num) hm0) hu0
  have hc2nn : 0 ≤ 24 * (m : ℝ) ^ 2 * r34 ^ m :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hu0
  -- exact values of the two derivatives
  have hcd : |ctermDeriv m φ| =
      24 * (m : ℝ) * r34 ^ m * |Real.sin ((m : ℝ) * φ)| / eterm m φ := by
    rw [ctermDeriv, abs_div, abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24), abs_of_nonneg hm0, abs_of_nonneg hu0,
        abs_of_pos hE_pos]
  have hcd2 : |ctermDeriv2 m φ| =
      24 * (m : ℝ) ^ 2 * r34 ^ m *
        |Real.cos ((m : ℝ) * φ) * (1 + (r34 ^ m) ^ 2) + 2 * r34 ^ m| / (eterm m φ) ^ 2 := by
    rw [ctermDeriv2, abs_div, abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24), abs_of_nonneg (sq_nonneg (m : ℝ)),
        abs_of_nonneg hu0, abs_of_pos (pow_pos hE_pos 2)]
  -- first derivative
  have hstep1 : 24 * (m : ℝ) * r34 ^ m * |Real.sin ((m : ℝ) * φ)| ≤ 24 * (m : ℝ) * r34 ^ m := by
    calc 24 * (m : ℝ) * r34 ^ m * |Real.sin ((m : ℝ) * φ)|
        = (24 * (m : ℝ) * r34 ^ m) * |Real.sin ((m : ℝ) * φ)| := by ring
      _ ≤ (24 * (m : ℝ) * r34 ^ m) * 1 := mul_le_mul_of_nonneg_left hsin_le hc1nn
      _ = 24 * (m : ℝ) * r34 ^ m := by ring
  have hA : |ctermDeriv m φ| ≤ 24 * (m : ℝ) * r34 ^ m / eterm m φ := by
    rw [hcd]; exact div_le_div_of_nonneg_right hstep1 (le_of_lt hE_pos)
  have hB : 24 * (m : ℝ) * r34 ^ m / eterm m φ ≤ 24 * (m : ℝ) * r34 ^ m / (1 - r34 ^ m) ^ 2 :=
    div_le_div_of_nonneg_left hc1nn hd_pos hE_lb
  -- second derivative
  have hstep2 : 24 * (m : ℝ) ^ 2 * r34 ^ m *
        |Real.cos ((m : ℝ) * φ) * (1 + (r34 ^ m) ^ 2) + 2 * r34 ^ m|
      ≤ 24 * (m : ℝ) ^ 2 * r34 ^ m * eterm m φ :=
    mul_le_mul_of_nonneg_left hnum hc2nn
  have hA2 : |ctermDeriv2 m φ| ≤ 24 * (m : ℝ) ^ 2 * r34 ^ m * eterm m φ / (eterm m φ) ^ 2 := by
    rw [hcd2]; exact div_le_div_of_nonneg_right hstep2 (pow_nonneg (le_of_lt hE_pos) 2)
  have hmideq : 24 * (m : ℝ) ^ 2 * r34 ^ m * eterm m φ / (eterm m φ) ^ 2
      = 24 * (m : ℝ) ^ 2 * r34 ^ m / eterm m φ := by
    field_simp
  have hB2 : 24 * (m : ℝ) ^ 2 * r34 ^ m / eterm m φ
      ≤ 24 * (m : ℝ) ^ 2 * r34 ^ m / (1 - r34 ^ m) ^ 2 :=
    div_le_div_of_nonneg_left hc2nn hd_pos hE_lb
  exact ⟨le_trans hA hB, le_trans (le_trans hA2 (le_of_eq hmideq)) hB2⟩

end Work.CNum
