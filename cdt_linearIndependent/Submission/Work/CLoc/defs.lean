import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.LocationSing

/-!
# Shared facts for the area CLoc (`Submission.CDTPlan.CLocation`)

Location of the singularities of the C-side operator with the NON-strict gap
`10⁶ |m − n| ≤ n`.  This module re-exports `Submission.CDT.LocationSing` (`sqP`, `sqM`, `ymap`
and its elementary estimates) and adds the bridge between the blueprint's `xRoot`/`yOf` and the
`sqP`/`sqM`/`ymap` vocabulary.
-/

namespace Work.CLoc

open Submission.CDTPlan
open Submission.CDT.LocationSing (sqP sqM ymap sqP_pos sqM_pos sqP_eq sqM_eq_inv
  sqP_sub_sqP_le four_mul_add_one_le_sqP sqP_le sqP_lt_sqP sqM_mul_sqP sqP_mul_sqM
  ymap_large_large ymap_small_small ymap_large_small ymap_small_large)

noncomputable section

/-- `sqM t = 2t + 1 - 2√(t(t+1))`. -/
lemma sqM_eq_alt (t : ℝ) (ht : 0 ≤ t) :
    sqM t = 2 * t + 1 - 2 * Real.sqrt (t * (t + 1)) := by
  have h1 : (Real.sqrt (t + 1)) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  have h2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have hsum : sqP t + sqM t = 4 * t + 2 := by
    unfold sqP sqM
    nlinarith [h1, h2, sq_nonneg (Real.sqrt (t + 1) + Real.sqrt t),
      sq_nonneg (Real.sqrt (t + 1) - Real.sqrt t)]
  have := sqP_eq t ht
  linarith [hsum, this]

/-- `√((2t+1)² − 1) = 2√(t(t+1))`. -/
lemma sqrt_sq_sub_one (t : ℝ) :
    Real.sqrt ((2 * t + 1) ^ 2 - 1) = 2 * Real.sqrt (t * (t + 1)) := by
  have h : (2 * t + 1) ^ 2 - 1 = 4 * (t * (t + 1)) := by ring
  rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]

/-- The `sa = 1` inner factor of `xRoot` is `sqP`. -/
lemma inner_one (t : ℕ) :
    2 * (t : ℝ) + 1 + 1 * Real.sqrt ((2 * (t : ℝ) + 1) ^ 2 - 1) = sqP (t : ℝ) := by
  rw [sqrt_sq_sub_one, one_mul, sqP_eq _ (by positivity)]

/-- The `sa = -1` inner factor of `xRoot` is `sqM`. -/
lemma inner_neg (t : ℕ) :
    2 * (t : ℝ) + 1 + (-1) * Real.sqrt ((2 * (t : ℝ) + 1) ^ 2 - 1) = sqM (t : ℝ) := by
  rw [sqrt_sq_sub_one, sqM_eq_alt _ (by positivity)]
  ring

lemma xRoot_pp (m n : ℕ) : xRoot m n 1 1 = sqP (m : ℝ) * sqP (n : ℝ) := by
  unfold xRoot
  rw [inner_one m, inner_one n]

lemma xRoot_pm (m n : ℕ) : xRoot m n 1 (-1) = sqP (m : ℝ) * sqM (n : ℝ) := by
  unfold xRoot
  rw [inner_one m, inner_neg n]

lemma xRoot_mp (m n : ℕ) : xRoot m n (-1) 1 = sqM (m : ℝ) * sqP (n : ℝ) := by
  unfold xRoot
  rw [inner_neg m, inner_one n]

lemma xRoot_mm (m n : ℕ) : xRoot m n (-1) (-1) = sqM (m : ℝ) * sqM (n : ℝ) := by
  unfold xRoot
  rw [inner_neg m, inner_neg n]

/-- `yOf` and `ymap` are the same function. -/
lemma yOf_eq_ymap (x : ℝ) : yOf x = ymap x := rfl

end

end Work.CLoc
