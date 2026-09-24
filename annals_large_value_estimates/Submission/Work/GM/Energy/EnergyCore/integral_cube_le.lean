import Mathlib

namespace Work.GM.Energy.EnergyCore

open MeasureTheory

/-- Hölder in the special case `p = 3`, `q = 3/2` (equivalently Jensen for the convex
function `t ↦ t³` on `[0,∞)`): the cube of the integral of a nonnegative continuous
function is at most `(b-a)²` times the integral of its cube. -/
theorem integral_cube_le {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc a b)) (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ h x) :
    (∫ x in a..b, h x) ^ 3 ≤ (b - a) ^ 2 * ∫ x in a..b, h x ^ 3 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · have hLpos : 0 < b - a := sub_pos.mpr hlt
    set L : ℝ := b - a with hL
    set A : ℝ := ∫ x in a..b, h x with hA
    set v : ℝ := A / L with hv
    have hLpos' : 0 < L := by rw [hL]; exact hLpos
    have hLne : L ≠ 0 := ne_of_gt hLpos'
    have hA0 : 0 ≤ A := by rw [hA]; exact intervalIntegral.integral_nonneg hlt.le h0
    have hv0 : 0 ≤ v := by rw [hv]; exact div_nonneg hA0 hLpos'.le
    -- tangent-line (supporting-line) inequality for the convex function `t ↦ t³` at `v`
    have hle : ∀ x ∈ Set.Icc a b, (3 * v ^ 2 * h x - 2 * v ^ 3) ≤ h x ^ 3 := by
      intro x hx
      have hx0 : 0 ≤ h x := h0 x hx
      nlinarith [mul_nonneg (sq_nonneg (h x - v)) (by linarith : (0:ℝ) ≤ h x + 2 * v)]
    have hf : IntervalIntegrable (fun x : ℝ => 3 * v ^ 2 * h x - 2 * v ^ 3) volume a b :=
      ((continuousOn_const.mul hh).sub continuousOn_const).intervalIntegrable_of_Icc hlt.le
    have hg : IntervalIntegrable (fun x : ℝ => h x ^ 3) volume a b :=
      (hh.pow 3).intervalIntegrable_of_Icc hlt.le
    -- the integral of the supporting line
    have hval : ∫ x in a..b, (3 * v ^ 2 * h x - 2 * v ^ 3) = v ^ 3 * L := by
      have h1 : IntervalIntegrable (fun x : ℝ => 3 * v ^ 2 * h x) volume a b :=
        (continuousOn_const.mul hh).intervalIntegrable_of_Icc hlt.le
      have h2 : IntervalIntegrable (fun _ : ℝ => 2 * v ^ 3) volume a b :=
        continuousOn_const.intervalIntegrable_of_Icc hlt.le
      rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      rw [← hA, ← hL, hv]
      field_simp
      ring
    have hmain : v ^ 3 * L ≤ ∫ x in a..b, h x ^ 3 := by
      rw [← hval]
      exact intervalIntegral.integral_mono_on hlt.le hf hg hle
    have hLv : L * v = A := by rw [hv]; exact mul_div_cancel₀ A hLne
    have hstep : L ^ 2 * (v ^ 3 * L) ≤ L ^ 2 * (∫ x in a..b, h x ^ 3) :=
      mul_le_mul_of_nonneg_left hmain (sq_nonneg L)
    have hkey : L ^ 2 * (v ^ 3 * L) = A ^ 3 := by rw [← hLv]; ring
    rw [hkey, hA, hL] at hstep
    exact hstep

end Work.GM.Energy.EnergyCore
