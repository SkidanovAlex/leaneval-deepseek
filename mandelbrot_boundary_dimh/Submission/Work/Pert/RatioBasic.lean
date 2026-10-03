import Mathlib

/-!
# Generic complex-norm estimates for `Work.Pert.ratio_sub_ratio_le`

Small reusable lemmas about `‖·‖` on `ℂ` (only the normed-field structure is used), for
bounding quotients of the shape `u / (1 + t * u)` appearing in Shishikura's perturbation
estimates (4.2.x).
-/

namespace Work.Pert

/-- Reverse triangle inequality, additive form: `‖1 + z‖ ≥ 1 - ‖z‖`. -/
lemma one_sub_norm_le_norm_one_add (z : ℂ) : 1 - ‖z‖ ≤ ‖1 + z‖ := by
  have h := abs_norm_sub_norm_le (1 : ℂ) (-z)
  rw [norm_one, norm_neg, sub_neg_eq_add] at h
  have h2 : (1 : ℝ) - ‖z‖ ≤ |(1 : ℝ) - ‖z‖| := le_abs_self _
  linarith

/-- `‖1 + z‖ ≥ ρ` as soon as `‖z‖ ≤ 1 - ρ`. -/
lemma le_norm_one_add {z : ℂ} {ρ : ℝ} (h : ‖z‖ ≤ 1 - ρ) : ρ ≤ ‖1 + z‖ := by
  have := one_sub_norm_le_norm_one_add z; linarith

/-- Quotient bound: if `‖a‖ ≤ r * rb` and `rb ≤ ‖b‖` with `rb > 0`, `r ≥ 0`, then `‖a / b‖ ≤ r`. -/
lemma norm_div_le_of {a b : ℂ} {rb r : ℝ} (hrb : 0 < rb) (hb : rb ≤ ‖b‖) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r * rb) : ‖a / b‖ ≤ r := by
  rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hrb hb)]
  exact le_trans ha (mul_le_mul_of_nonneg_left hb hr)

/-- Three-term triangle inequality: `‖a - b‖ ≤ ‖a - c‖ + ‖c - b‖`. -/
lemma norm_sub_le_of_sub (a b c : ℂ) : ‖a - b‖ ≤ ‖a - c‖ + ‖c - b‖ := by
  have h : a - b = (a - c) + (c - b) := by ring
  rw [h]; exact norm_add_le _ _

/-- Four-term triangle inequality: `‖a - b‖ ≤ ‖a - c‖ + ‖c - d‖ + ‖d - b‖`. -/
lemma norm_sub_le_of_sub_sub (a b c d : ℂ) :
    ‖a - b‖ ≤ ‖a - c‖ + ‖c - d‖ + ‖d - b‖ := by
  have h : a - b = (a - c) + (c - d) + (d - b) := by ring
  rw [h]
  calc ‖(a - c) + (c - d) + (d - b)‖ ≤ ‖(a - c) + (c - d)‖ + ‖d - b‖ := norm_add_le _ _
    _ ≤ (‖a - c‖ + ‖c - d‖) + ‖d - b‖ := by
        have := norm_add_le (a - c) (c - d); linarith

end Work.Pert
