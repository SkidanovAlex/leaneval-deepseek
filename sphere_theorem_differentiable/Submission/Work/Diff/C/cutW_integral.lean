import Mathlib
import Submission.Work.Diff.C.cutoff_psi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral of the transition profile `cutW`

`cutW u = (3/2) * smoothTransition (2u) - (1/2) * smoothTransition (2u - 1)`, so
`∫ u in 0..1, cutW u = (3/2) * (3/4) - (1/2) * (1/4) = 1`.

The two ingredients are

* the symmetry `smoothTransition x + smoothTransition (1 - x) = 1`, which gives
  `∫ x in 0..1, smoothTransition x = 1/2`;
* the affine substitutions `u ↦ 2u` and `u ↦ 2u - 1`.
-/

namespace Work.Diff.C

open MeasureTheory

/-- Symmetry of the smooth transition: `smoothTransition x + smoothTransition (1 - x) = 1`. -/
lemma smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [Real.smoothTransition.zero_of_nonpos hx,
      Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 1 - x by linarith)]
    norm_num
  · rcases le_or_gt 1 x with hx1 | hx1
    · rw [Real.smoothTransition.one_of_one_le hx1,
        Real.smoothTransition.zero_of_nonpos (show (1 : ℝ) - x ≤ 0 by linarith)]
      norm_num
    · have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
        (Real.smoothTransition.pos_denom x).ne'
      unfold Real.smoothTransition
      rw [show (1 : ℝ) - (1 - x) = x by ring]
      rw [show expNegInvGlue (1 - x) + expNegInvGlue x
            = expNegInvGlue x + expNegInvGlue (1 - x) by ring]
      field_simp

/-- `∫ x in 0..1, smoothTransition x = 1/2`, by the symmetry `x ↦ 1 - x`. -/
lemma integral_smoothTransition_zero_one :
    (∫ x in (0 : ℝ)..1, Real.smoothTransition x) = 1 / 2 := by
  have h1 : (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x))
      = ∫ x in (0 : ℝ)..1, Real.smoothTransition x := by
    rw [intervalIntegral.integral_comp_sub_left _ 1]
    norm_num
  have h2 : (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x))
      = ∫ x in (0 : ℝ)..1, (1 - Real.smoothTransition x) := by
    apply intervalIntegral.integral_congr
    intro x _
    linarith [smoothTransition_add_one_sub x]
  have h3 : (∫ x in (0 : ℝ)..1, (1 - Real.smoothTransition x))
      = 1 - ∫ x in (0 : ℝ)..1, Real.smoothTransition x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)]
    rw [intervalIntegral.integral_const]
    simp
  linarith [h1, h2, h3]

/-- `∫ x in 1..2, smoothTransition x = 1`, since `smoothTransition x = 1` for `x ≥ 1`. -/
lemma integral_smoothTransition_one_two :
    (∫ x in (1 : ℝ)..2, Real.smoothTransition x) = 1 := by
  have h : (∫ x in (1 : ℝ)..2, Real.smoothTransition x) = ∫ x in (1 : ℝ)..2, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    refine Real.smoothTransition.one_of_one_le ?_
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    exact hx.1
  rw [h, intervalIntegral.integral_const]
  norm_num

/-- `∫ x in 0..2, smoothTransition x = 3/2`. -/
lemma integral_smoothTransition_zero_two :
    (∫ x in (0 : ℝ)..2, Real.smoothTransition x) = 3 / 2 := by
  have hadj : (∫ x in (0 : ℝ)..1, Real.smoothTransition x)
      + ∫ x in (1 : ℝ)..2, Real.smoothTransition x
      = ∫ x in (0 : ℝ)..2, Real.smoothTransition x :=
    intervalIntegral.integral_add_adjacent_intervals
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)
      (Real.smoothTransition.continuous.intervalIntegrable 1 2)
  rw [← hadj, integral_smoothTransition_zero_one, integral_smoothTransition_one_two]
  norm_num

/-- `∫ x in -1..0, smoothTransition x = 0`. -/
lemma integral_smoothTransition_neg_one_zero :
    (∫ x in (-1 : ℝ)..0, Real.smoothTransition x) = 0 := by
  have h : (∫ x in (-1 : ℝ)..0, Real.smoothTransition x)
      = ∫ x in (-1 : ℝ)..0, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    refine Real.smoothTransition.zero_of_nonpos ?_
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    exact hx.2
  rw [h, intervalIntegral.integral_zero]

/-- `∫ x in -1..1, smoothTransition x = 1/2`. -/
lemma integral_smoothTransition_neg_one_one :
    (∫ x in (-1 : ℝ)..1, Real.smoothTransition x) = 1 / 2 := by
  have hadj : (∫ x in (-1 : ℝ)..0, Real.smoothTransition x)
      + ∫ x in (0 : ℝ)..1, Real.smoothTransition x
      = ∫ x in (-1 : ℝ)..1, Real.smoothTransition x :=
    intervalIntegral.integral_add_adjacent_intervals
      (Real.smoothTransition.continuous.intervalIntegrable (-1) 0)
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)
  rw [← hadj, integral_smoothTransition_neg_one_zero, integral_smoothTransition_zero_one]
  norm_num

/-- `∫ u in 0..1, smoothTransition (2u) = 3/4`. -/
lemma integral_smoothTransition_two_mul :
    (∫ u in (0 : ℝ)..1, Real.smoothTransition (2 * u)) = 3 / 4 := by
  have hcomp : (∫ u in (0 : ℝ)..1, Real.smoothTransition (2 * u))
      = (2 : ℝ)⁻¹ * ∫ x in (0 : ℝ)..2, Real.smoothTransition x := by
    rw [intervalIntegral.integral_comp_mul_left _ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hcomp, integral_smoothTransition_zero_two]
  norm_num

/-- `∫ u in 0..1, smoothTransition (2u - 1) = 1/4`. -/
lemma integral_smoothTransition_two_mul_sub_one :
    (∫ u in (0 : ℝ)..1, Real.smoothTransition (2 * u - 1)) = 1 / 4 := by
  have hcomp : (∫ u in (0 : ℝ)..1, Real.smoothTransition (2 * u - 1))
      = (2 : ℝ)⁻¹ * ∫ x in (-1 : ℝ)..1, Real.smoothTransition x := by
    rw [intervalIntegral.integral_comp_mul_sub _ (by norm_num : (2 : ℝ) ≠ 0) 1]
    norm_num
  rw [hcomp, integral_smoothTransition_neg_one_one]
  norm_num

theorem cutW_integral : (∫ u in (0 : ℝ)..1, cutW u) = 1 := by
  have h1 : IntervalIntegrable (fun u : ℝ => (3 / 2 : ℝ) * Real.smoothTransition (2 * u))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h2 : IntervalIntegrable (fun u : ℝ => (1 / 2 : ℝ) * Real.smoothTransition (2 * u - 1))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp only [cutW]
  rw [intervalIntegral.integral_sub h1 h2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_smoothTransition_two_mul, integral_smoothTransition_two_mul_sub_one]
  norm_num

end Work.Diff.C
