import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.AlpBound

/-!
# `Work.CNum.DAux.SinHalfBound`

At the grid angle `θ = 245 π / 1024` the quantity `C2w (245 π / 512) = √(sin θ² - σ²)`
(where `σ = C2σ = sin (alpR/2)`) is at least `1/300`, provided `θ` overshoots the cusp
half-angle `alpR / 2` by at least `1/1000`.

The proof is the elementary factorisation `sin²θ - sin²a = sin (θ + a) · sin (θ - a)`
together with two Jordan-type lower bounds `sin x ≥ (2/π) x` on `[0, π/2]`:
the hypotheses place `θ + a ≥ 1.49` and `θ - a ≥ 1/1000`, whence
`sin²θ - sin²a ≥ (9/10)·(1/2000) = 9/20000 ≥ 1/90000 = (1/300)²`.
-/

namespace Work.CNum.DAux

open Work.CNum

/-- **Core trigonometric lower bound.**  If `θ - a ≥ 1/1000`, `θ + a ≥ 1.49` and both
`θ + a` and `θ - a` lie below `π/2`, then `sin²θ - sin²a ≥ 1/90000`. -/
private theorem sinSqSubLower_local {θ a : ℝ}
    (hδ : (1 : ℝ) / 1000 ≤ θ - a)
    (hlo : (1.49 : ℝ) ≤ θ + a)
    (hhi : θ + a ≤ Real.pi / 2)
    (hu : θ - a ≤ Real.pi / 2) :
    (1 : ℝ) / 90000 ≤ Real.sin θ ^ 2 - Real.sin a ^ 2 := by
  have hd0 : 0 ≤ θ - a := by linarith
  have hs0 : 0 ≤ θ + a := by linarith
  have hid : Real.sin θ ^ 2 - Real.sin a ^ 2 = Real.sin (θ + a) * Real.sin (θ - a) := by
    rw [Real.sin_add, Real.sin_sub]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq a]
  have hsin_s : (9 : ℝ) / 10 ≤ Real.sin (θ + a) := by
    have h2pi_pos : (0 : ℝ) < 2 / Real.pi := by positivity
    have h1 : 2 / Real.pi * (1.49 : ℝ) ≤ 2 / Real.pi * (θ + a) :=
      mul_le_mul_of_nonneg_left hlo h2pi_pos.le
    have h2 : (9 : ℝ) / 10 ≤ 2 / Real.pi * (1.49 : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_d4]
    have h3 := Real.mul_le_sin hs0 hhi
    linarith
  have hsin_d : (1 : ℝ) / 2000 ≤ Real.sin (θ - a) := by
    have h2pi_pos : (0 : ℝ) < 2 / Real.pi := by positivity
    have h1 : 2 / Real.pi * ((1 : ℝ) / 1000) ≤ 2 / Real.pi * (θ - a) :=
      mul_le_mul_of_nonneg_left hδ h2pi_pos.le
    have h2 : (1 : ℝ) / 2000 ≤ 2 / Real.pi * ((1 : ℝ) / 1000) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_d4]
    have h3 := Real.mul_le_sin hd0 hu
    linarith
  rw [hid]
  have hb : (0 : ℝ) ≤ Real.sin (θ + a) := by linarith
  calc (1 : ℝ) / 90000 ≤ (9 : ℝ) / 10 * ((1 : ℝ) / 2000) := by norm_num
    _ ≤ Real.sin (θ + a) * Real.sin (θ - a) :=
        mul_le_mul hsin_s hsin_d (by norm_num) hb

theorem SinHalfBound (hδ : (1 : ℝ) / 1000 ≤ 245 * Real.pi / 1024 - Work.CNum.alpR / 2) :
    (1 : ℝ) / 300 ≤ Real.sqrt (Real.sin (245 * Real.pi / 1024) ^ 2 - Work.CNum.C2σ ^ 2) := by
  have hAlp := Work.CNum.AlpBound
  have h1 : (1.49 : ℝ) ≤ 245 * Real.pi / 1024 + Work.CNum.alpR / 2 := by
    nlinarith [Real.pi_gt_d4, hAlp.1]
  have h2 : 245 * Real.pi / 1024 + Work.CNum.alpR / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_d4, Real.pi_lt_d4, hAlp.2]
  have h3 : 245 * Real.pi / 1024 - Work.CNum.alpR / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_d4, Real.pi_lt_d4, hAlp.1]
  have hcore := sinSqSubLower_local (θ := 245 * Real.pi / 1024) (a := Work.CNum.alpR / 2)
    hδ h1 h2 h3
  have hC2 : Work.CNum.C2σ = Real.sin (Work.CNum.alpR / 2) := Work.CNum.sin_half_alpR.symm
  have hsq : ((1 : ℝ) / 300) ^ 2 ≤
      Real.sin (245 * Real.pi / 1024) ^ 2 - Work.CNum.C2σ ^ 2 := by
    have hA : ((1 : ℝ) / 300) ^ 2 = 1 / 90000 := by norm_num
    rw [hA, hC2]
    exact hcore
  have hb : (0 : ℝ) ≤ Real.sin (245 * Real.pi / 1024) ^ 2 - Work.CNum.C2σ ^ 2 := by
    linarith
  exact (Real.le_sqrt (by norm_num) hb).mpr hsq

end Work.CNum.DAux
