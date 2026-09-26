import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace

/-!
# The `psiA1` window functional at four Pythagorean angles

The `A`-branch of the plane trace meets the `y`-faces of the box `PBox` when the window
functional

`psiA1 u = 3 * |trN1 u| - yclip * (2 * (97/100) - trS u)`

changes sign.  At the four Pythagorean angles used to bracket the first and the last crossing
of the `y`-face -- `ang (7/10)`, `ang (5/2)`, `ang 5` and `ang 14` -- the trigonometric
quantities are rational (because `cos (ang t) = (1-t^2)/(1+t^2)` and `sin (ang t) = 2t/(1+t^2)`
for rational `t`), and `trS` is a square root of a rational number.  This module evaluates the
sign of the (signed) functional at those four angles, which is exactly the arithmetic input
needed to certify that the `A`-branch enters the box at `ang (7/10)` and leaves it between
`ang 5` and `ang 14` on its first passage.

The four signs proved are

* `psiA1 (ang (7/10)) > 0` (with `trN1 (ang (7/10)) > 0`),
* `psiA1 (ang (5/2)) < 0`,
* `psiA1 (ang 5) < 0` (written with `-trN1`, since `trN1 (ang 5) < 0`),
* `psiA1 (ang 14) > 0` (written with `-trN1`, since `trN1 (ang 14) < 0`).
-/

namespace Work.RefuteDrop

open Work.BoxShrink.PinchOff.RefuteDrop

/-! ## Evaluating `trN1` and `trA` at `ang t` -/

lemma trN1_eq_cos_sin (u : ℝ) :
    trN1 u = (7761/10000) * Real.cos u + (4907/5000) * Real.sin u := by
  simp only [trN1, trB1, trA]; ring

lemma trN1_ang (t : ℝ) :
    trN1 (ang t) = ((7761/10000) * (1 - t^2) + (4907/5000) * (2*t)) / (1 + t^2) := by
  rw [trN1_eq_cos_sin, cos_ang, sin_ang]; ring

lemma trA_ang (t : ℝ) :
    trA (ang t) = (-(2/25) * (1 - t^2) - (39/100) * (2*t)) / (1 + t^2) := by
  rw [trA, cos_ang, sin_ang]; ring

lemma trN1_ang_seven_tenths : trN1 (ang (7/10)) = 1769771/1490000 := by
  rw [trN1_ang]; norm_num

lemma trN1_ang_five_halves : trN1 (ang (5/2)) = 33299/290000 := by
  rw [trN1_ang]; norm_num

lemma trN1_ang_five : trN1 (ang 5) = -22031/65000 := by
  rw [trN1_ang]; norm_num

lemma trN1_ang_fourteen : trN1 (ang 14) = -1238603/1970000 := by
  rw [trN1_ang]; norm_num

lemma trA_ang_fourteen : trA (ang 14) = 468/19700 := by
  rw [trA_ang]; norm_num

/-! ## Bounds for `trS` and `yclip` -/

/-- A rational lower bound for the `trS` value at the last angle `ang 14`. -/
lemma trS_ang_fourteen_gt : (969/1000 : ℝ) < trS (ang 14) := by
  rw [trS, Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 969/1000), trA_ang_fourteen]
  norm_num

/-- The rational bound `2^{1/3} < 63/50`. -/
lemma rpow_third_lt : (2:ℝ)^(1/3:ℝ) < 63/50 := by
  have h3 : (2:ℝ) < ((63/50 : ℝ) ^ ((3:ℕ):ℝ)) := by
    rw [Real.rpow_natCast]; norm_num
  have h := (Real.rpow_lt_rpow_iff (by norm_num : (0:ℝ) ≤ 2) (by positivity)
    (by norm_num : (0:ℝ) < (1/3:ℝ))).mpr h3
  have h2 : (((63/50 : ℝ) ^ ((3:ℕ):ℝ)))^(1/3:ℝ) = 63/50 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (63/50:ℝ))]
    norm_num
  rwa [h2] at h

/-- An upper bound for the `y`-window half-width `yclip = (7/5) * 2^{1/3}`. -/
lemma yclip_upper : yclip < 1764/1000 := by
  rw [yclip]; nlinarith [rpow_third_lt]

/-! ## The four evaluations -/

theorem psiA1_evals :
    (0 < 3 * Work.BoxShrink.PinchOff.RefuteDrop.trN1 (Work.BoxShrink.PinchOff.RefuteDrop.ang (7/10)) - Work.BoxShrink.PinchOff.RefuteDrop.yclip * (2*(97/100) - Work.BoxShrink.PinchOff.RefuteDrop.trS (Work.BoxShrink.PinchOff.RefuteDrop.ang (7/10)))) ∧
    (3 * Work.BoxShrink.PinchOff.RefuteDrop.trN1 (Work.BoxShrink.PinchOff.RefuteDrop.ang (5/2)) - Work.BoxShrink.PinchOff.RefuteDrop.yclip * (2*(97/100) - Work.BoxShrink.PinchOff.RefuteDrop.trS (Work.BoxShrink.PinchOff.RefuteDrop.ang (5/2))) < 0) ∧
    (-3 * Work.BoxShrink.PinchOff.RefuteDrop.trN1 (Work.BoxShrink.PinchOff.RefuteDrop.ang 5) - Work.BoxShrink.PinchOff.RefuteDrop.yclip * (2*(97/100) - Work.BoxShrink.PinchOff.RefuteDrop.trS (Work.BoxShrink.PinchOff.RefuteDrop.ang 5)) < 0) ∧
    (0 < -3 * Work.BoxShrink.PinchOff.RefuteDrop.trN1 (Work.BoxShrink.PinchOff.RefuteDrop.ang 14) - Work.BoxShrink.PinchOff.RefuteDrop.yclip * (2*(97/100) - Work.BoxShrink.PinchOff.RefuteDrop.trS (Work.BoxShrink.PinchOff.RefuteDrop.ang 14))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `u = ang (7/10)`: `trS` is small, so the `yclip` term cannot dominate.
    rw [trN1_ang_seven_tenths]
    have hS : trS (ang (7/10)) ≤ 97/100 := trS_le _
    have hSnn : 0 ≤ trS (ang (7/10)) := trS_nonneg _
    have hy : yclip < 1764/1000 := yclip_upper
    have hyl : (1762/1000 : ℝ) < yclip := yclip_lower
    nlinarith [hS, hSnn, hy, hyl]
  · -- `u = ang (5/2)`: `trS ≤ 97/100`, so the `yclip` term is bounded below.
    rw [trN1_ang_five_halves]
    have hS : trS (ang (5/2)) ≤ 97/100 := trS_le _
    have hy : (1762/1000 : ℝ) < yclip := yclip_lower
    nlinarith [hS, hy]
  · -- `u = ang 5`: `trN1 < 0` and `trS ≤ 97/100`.
    rw [trN1_ang_five]
    have hS : trS (ang 5) ≤ 97/100 := trS_le _
    have hy : (1762/1000 : ℝ) < yclip := yclip_lower
    nlinarith [hS, hy]
  · -- `u = ang 14`: `trS` is bounded below by `969/1000`, so the `yclip` term stays below
    -- `(1764/1000) * (971/1000)`.
    rw [trN1_ang_fourteen]
    have hS : (969/1000 : ℝ) < trS (ang 14) := trS_ang_fourteen_gt
    have hy : yclip < 1764/1000 := yclip_upper
    have hypos : 0 < yclip := by linarith [yclip_lower]
    have hprod : yclip * (2*(97/100) - trS (ang 14)) < (1764/1000) * (971/1000) := by
      have h1 : 2*(97/100) - trS (ang 14) < 971/1000 := by linarith
      calc yclip * (2*(97/100) - trS (ang 14)) < yclip * (971/1000) :=
            mul_lt_mul_of_pos_left h1 hypos
        _ < (1764/1000) * (971/1000) := by
            apply mul_lt_mul_of_pos_right hy; norm_num
    nlinarith [hprod]

end Work.RefuteDrop
