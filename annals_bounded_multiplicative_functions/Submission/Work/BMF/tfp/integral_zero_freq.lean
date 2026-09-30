import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.tfp

open MeasureTheory intervalIntegral

/-- The real triangle integral: `∫_{x=-1}^{1} (1 - |x|) dx = 1`.
Split the interval at `0`; on `[-1,0]` use `|x| = -x` and substitute `x ↦ x + 1` to reduce to
`∫_{0}^{1} x`, on `[0,1]` use `|x| = x` and substitute `x ↦ 1 - x` likewise.  Each half is `1/2`. -/
lemma integral_one_sub_abs : ∫ x in (-1:ℝ)..1, (1 - |x|) = 1 := by
  have h1 : ∫ x in (-1:ℝ)..0, (1 - |x|) = 1 / 2 := by
    have hEq : Set.EqOn (fun x : ℝ => 1 - |x|) (fun x : ℝ => x + 1) (Set.uIcc (-1) 0) := by
      intro x hx
      show 1 - |x| = x + 1
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
      rw [abs_of_nonpos (by linarith [hx.2] : x ≤ 0)]
      ring
    rw [intervalIntegral.integral_congr hEq]
    rw [intervalIntegral.integral_comp_add_right (f := fun y : ℝ => y) (d := 1)]
    norm_num
  have h2 : ∫ x in (0:ℝ)..1, (1 - |x|) = 1 / 2 := by
    have hEq : Set.EqOn (fun x : ℝ => 1 - |x|) (fun x : ℝ => 1 - x) (Set.uIcc (0:ℝ) 1) := by
      intro x hx
      show 1 - |x| = 1 - x
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      rw [abs_of_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x)]
    rw [intervalIntegral.integral_congr hEq]
    rw [intervalIntegral.integral_comp_sub_left (f := fun y : ℝ => y) (d := 1)]
    norm_num
  have hcont : Continuous fun x : ℝ => 1 - |x| := continuous_const.sub continuous_abs
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := fun x : ℝ => 1 - |x|) (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)
  rw [h1, h2] at hadd
  linarith

/-- The zero-frequency case of the Fourier integral of the triangle function:
`∫_{x=-1}^{1} (1-|x|) dx = 1`, written with a `Complex.exp (0 * x)` factor so that it matches the
integrand of the general-frequency statement.  Split at `0`, `abs_of_nonpos`/`abs_of_nonneg`, and
two polynomial interval integrals (`1/2 + 1/2`). -/
lemma integral_zero_freq :
    ∫ x in (-1:ℝ)..1, (((1 - |x| : ℝ) : ℂ) * Complex.exp (0 * (x:ℂ))) = 1 := by
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, integral_one_sub_abs]
  norm_num

end Work.BMF.tfp
