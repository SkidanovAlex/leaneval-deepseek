/-
# `RadGreenSupp.Consts` — the constant of `radGreen_supp_weight_le`, and its arithmetic

The target bound

  `|radGreen α m c z| ≤ C · M · z ^ (2/α) / (1+z) ^ (7/α)`

(for `c` supported in `[a,b] ⊂ (0,∞)`, `|c| ≤ M`, `m ≥ 1`) is assembled from three regime
estimates, each supplying one summand of the constant

  `C α a b = (1/2)·a^(-2/α)·(1+a)^(7/α) + (1/14)·a^(-2/α)·(1+b)^(7/α)
              + (1/63)·(1+b)^(7/α)·b^(-2/α)`

(`z ≤ a`, `a ≤ z ≤ b`, `b ≤ z` respectively).  This module fixes `C`, proves it positive, records
that each summand is dominated by `C`, and collects the elementary arithmetic of
`rgK = 1/(α(4m+5))`, `rgP = 2m/α`, `rgQ = (2m+5)/α` that the three regime estimates use:

* `rgK/rgP = 1/(2m(4m+5)) ≤ 1/2`,  `rgK/rgQ = 1/((4m+5)(2m+5)) ≤ 1/63`,
  `rgK·(1/rgQ + 1/rgP) ≤ 1/18 + 1/63 = 1/14`   (`m ≥ 1`);
* `rgP ≥ 2/α`, `rgQ ≥ 7/α`  (`m ≥ 1`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

set_option autoImplicit false

/-- The constant of the weighted support bound for the radial Green function. -/
def C (α a b : ℝ) : ℝ :=
  (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)
    + (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α)
    + (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α))

theorem C_pos {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) : 0 < C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 < a ^ (-(2 / α)) := Real.rpow_pos_of_pos ha _
  have h2 : 0 < (1 + a) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have h3 : 0 < (1 + b) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have h4 : 0 < b ^ (-(2 / α)) := Real.rpow_pos_of_pos hb _
  simp only [C]
  positivity

theorem C_term1_le {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) ≤ C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ a ^ (-(2 / α)) := (Real.rpow_pos_of_pos ha _).le
  have h2 : 0 ≤ (1 + a) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h3 : 0 ≤ (1 + b) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ b ^ (-(2 / α)) := (Real.rpow_pos_of_pos hb _).le
  have h5 : 0 ≤ (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) := by positivity
  have h6 : 0 ≤ (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) := by positivity
  simp only [C]
  linarith

theorem C_term2_le {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) ≤ C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ a ^ (-(2 / α)) := (Real.rpow_pos_of_pos ha _).le
  have h2 : 0 ≤ (1 + a) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h3 : 0 ≤ (1 + b) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ b ^ (-(2 / α)) := (Real.rpow_pos_of_pos hb _).le
  have h5 : 0 ≤ (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) := by positivity
  have h6 : 0 ≤ (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) := by positivity
  simp only [C]
  linarith

theorem C_term3_le {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) ≤ C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ a ^ (-(2 / α)) := (Real.rpow_pos_of_pos ha _).le
  have h2 : 0 ≤ (1 + a) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h3 : 0 ≤ (1 + b) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ b ^ (-(2 / α)) := (Real.rpow_pos_of_pos hb _).le
  have h5 : 0 ≤ (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) := by positivity
  have h6 : 0 ≤ (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) := by positivity
  simp only [C]
  linarith

theorem rgK_div_rgP_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m ≤ 1 / 18 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heq : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
    rw [Work.FTS.EllExist.rgK, Work.FTS.EllExist.rgP]
    field_simp
  rw [heq]
  refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 18) ?_
  nlinarith

theorem rgK_div_rgQ_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m ≤ 1 / 63 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heq : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5)) := by
    rw [Work.FTS.EllExist.rgK, Work.FTS.EllExist.rgQ]
    field_simp
  rw [heq]
  refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 63) ?_
  nlinarith

theorem rgK_mul_inv_add_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.EllExist.rgK α m
        * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m) ≤ 1 / 14 := by
  have hP : 0 < Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_pos hα hm
  have hQ : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have h1 := rgK_div_rgP_le hα hm
  have h2 := rgK_div_rgQ_le hα hm
  have heq : Work.FTS.EllExist.rgK α m
        * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
      = Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m
        + Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m := by
    rw [mul_add, mul_one_div, mul_one_div]
  rw [heq]
  linarith

theorem two_div_alpha_le_rgP {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    2 / α ≤ Work.FTS.EllExist.rgP α m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.FTS.EllExist.rgP, div_le_div_iff_of_pos_right hα]
  linarith

theorem seven_div_alpha_le_rgQ {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    7 / α ≤ Work.FTS.EllExist.rgQ α m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.FTS.EllExist.rgQ, div_le_div_iff_of_pos_right hα]
  linarith

end Work.FTS.PhiStar.Honesty.RadGreenSupp
