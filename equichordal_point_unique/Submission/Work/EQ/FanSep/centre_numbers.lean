import Mathlib
import Submission.Work.EQ.FanSep.Defs

/-!
# Centre estimates for the fan separation

The stable fan `Work.EQ.fan a h ε` has its centre `fan a h ε 0` on the axis coset
`-1/2 + 2ℤ` (this file does not prove that, it only records the two *elementary numeric*
facts about the points of that coset used by the extreme-property argument of the uniform
fan separation `Work.EQ.fan_sep`).

Write `c_k = -1/2 + 2k` for `k : ℤ` and put `λ = eqLam a = (1-a)/(1+a)`.  For `0 < a < 1`:

* both distances `|c_k ∓ a/2|` are at least `(1-a)/2` (nothing about integrality of `k` is
  needed here except that `|2k| ≥ 2` for `k ≠ 0`);
* the *extreme property* `λ · |c_k - a/2| ≤ |c_k + a/2|` holds, with equality for `k = 0`.

These are the real inequalities underlying Rychlik's remark that the axis points of
`-1/2 + 2ℤ` are "far" from `±a/2` and that the point `-1/2` is the one where the ratio
`|c - a/2| / |c + a/2|` is maximal.
-/

namespace Work.EQ.FanSep

open Complex

noncomputable section

/-- `‖(r : ℂ) + (u : ℂ)‖ = |r + u|` for real `r, u`. -/
lemma norm_ofReal_add_eq_abs (r u : ℝ) : ‖((r : ℝ) : ℂ) + ((u : ℝ) : ℂ)‖ = |r + u| := by
  rw [← Complex.ofReal_add]
  exact RCLike.norm_ofReal _

/-- `‖(r : ℂ) - (u : ℂ)‖ = |r - u|` for real `r, u`. -/
lemma norm_ofReal_sub_eq_abs (r u : ℝ) : ‖((r : ℝ) : ℂ) - ((u : ℝ) : ℂ)‖ = |r - u| := by
  rw [← Complex.ofReal_sub]
  exact RCLike.norm_ofReal _

/-- For `0 < c < 1` and every integer `k`, the even integer `2k` is at distance at least `c`
from `c`: either `k = 0` and the distance is exactly `c`, or `|2k| ≥ 2` and the distance is
at least `1 ≥ c`. -/
lemma le_abs_int_sub {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (k : ℤ) :
    c ≤ |2 * (k : ℝ) - c| := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hkR : (k : ℝ) ≤ -1 := by
      have h : k ≤ -1 := by omega
      exact_mod_cast h
    have hlt : 2 * (k : ℝ) - c < 0 := by linarith
    rw [abs_of_neg hlt]
    linarith
  · subst hk
    rw [show (2 : ℝ) * ((0 : ℤ) : ℝ) - c = -c from by ring, abs_neg, abs_of_pos hc0]
  · have hkR : (1 : ℝ) ≤ (k : ℝ) := by
      have h : (1 : ℤ) ≤ k := by omega
      exact_mod_cast h
    have hpos : 0 < 2 * (k : ℝ) - c := by linarith
    rw [abs_of_pos hpos]
    linarith

/-- The extreme property: for `0 < c ≤ b < 1` and every integer `k`,
`(c/b) * |2k - b| ≤ |2k - c|`.  This is the quantitative content of the fact that among the
axis points `c_k = 2k` of `2ℤ` the point `0` maximises the ratio of the distances to `c` and
to `b` (where it is exactly `c/b`). -/
lemma ratio_mul_abs_le {b c : ℝ} (hc0 : 0 < c) (hcb : c ≤ b) (hb1 : b < 1) (k : ℤ) :
    (c / b) * |2 * (k : ℝ) - b| ≤ |2 * (k : ℝ) - c| := by
  have hb0 : 0 < b := lt_of_lt_of_le hc0 hcb
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hratio : c / b ≤ 1 := by rw [div_le_one hb0]; exact hcb
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hkR : (k : ℝ) ≤ -1 := by
      have h : k ≤ -1 := by omega
      exact_mod_cast h
    have hbneg : 2 * (k : ℝ) - b < 0 := by linarith
    have hcneg : 2 * (k : ℝ) - c < 0 := by linarith
    rw [abs_of_neg hbneg, abs_of_neg hcneg, neg_sub, neg_sub, mul_sub,
      div_mul_cancel₀ c hbne]
    have hle : (c / b) * (2 * (k : ℝ)) ≥ 2 * (k : ℝ) := by
      have h2k : 2 * (k : ℝ) ≤ 0 := by linarith
      calc 2 * (k : ℝ) = 1 * (2 * (k : ℝ)) := by ring
        _ ≤ (c / b) * (2 * (k : ℝ)) := mul_le_mul_of_nonpos_right hratio h2k
    linarith
  · subst hk
    simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg]
    rw [abs_of_pos hb0, abs_of_pos hc0, div_mul_cancel₀ c hbne]
  · have hkR : (1 : ℝ) ≤ (k : ℝ) := by
      have h : (1 : ℤ) ≤ k := by omega
      exact_mod_cast h
    have hbpos : 0 < 2 * (k : ℝ) - b := by linarith
    have hcpos : 0 < 2 * (k : ℝ) - c := by linarith
    rw [abs_of_pos hbpos, abs_of_pos hcpos, mul_sub, div_mul_cancel₀ c hbne]
    have hle : (c / b) * (2 * (k : ℝ)) ≤ 2 * (k : ℝ) := by
      have h2k : 0 ≤ 2 * (k : ℝ) := by linarith
      calc (c / b) * (2 * (k : ℝ)) ≤ 1 * (2 * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hratio h2k
        _ = 2 * (k : ℝ) := by ring
    linarith

theorem centre_numbers {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ k : ℤ, (1 - a) / 2 ≤ ‖((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ ∧
               (1 - a) / 2 ≤ ‖((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖) ∧
    ∀ k : ℤ, eqLam a * ‖((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ ≤
               ‖((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := by
  have hca0 : 0 < (1 - a) / 2 := by linarith
  have hca1 : (1 - a) / 2 < 1 := by linarith
  have hcb0 : 0 < (1 + a) / 2 := by linarith
  have hcb1 : (1 + a) / 2 < 1 := by linarith
  have hcba : (1 - a) / 2 ≤ (1 + a) / 2 := by linarith
  have hratio : ((1 - a) / 2) / ((1 + a) / 2) = eqLam a := by
    rw [eqLam]; field_simp
  constructor
  · intro k
    constructor
    · rw [norm_ofReal_add_eq_abs]
      rw [show (-1 / 2 + 2 * (k : ℝ)) + a / 2 = 2 * (k : ℝ) - (1 - a) / 2 from by ring]
      exact le_abs_int_sub hca0 hca1 k
    · rw [norm_ofReal_sub_eq_abs]
      rw [show (-1 / 2 + 2 * (k : ℝ)) - a / 2 = 2 * (k : ℝ) - (1 + a) / 2 from by ring]
      exact le_trans hcba (le_abs_int_sub hcb0 hcb1 k)
  · intro k
    rw [norm_ofReal_sub_eq_abs, norm_ofReal_add_eq_abs]
    rw [show (-1 / 2 + 2 * (k : ℝ)) - a / 2 = 2 * (k : ℝ) - (1 + a) / 2 from by ring]
    rw [show (-1 / 2 + 2 * (k : ℝ)) + a / 2 = 2 * (k : ℝ) - (1 - a) / 2 from by ring]
    rw [← hratio]
    exact ratio_mul_abs_le hca0 hcba hcb1 k

end

end Work.EQ.FanSep
