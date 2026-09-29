import Mathlib
import Submission.Work.Cert.Spec

namespace Work.Cert.ACTrig

open Complex

/-- `rot t = e^{2πit}` is 1-Lipschitz for the circle metric: the chord length between
`rot u` and `rot v` is at most the arc length `2π|u-v|`. -/
theorem rot_dist_le (Rr u v : ℝ) (hR : 0 ≤ Rr) :
    ‖Rr * Submission.CDTPlan.rot u - Rr * Submission.CDTPlan.rot v‖ ≤ 2 * Real.pi * Rr * |u - v| := by
  -- `‖rot t‖ = 1`
  have hrot1 : ∀ t : ℝ, ‖Submission.CDTPlan.rot t‖ = 1 := by
    intro t
    rw [Submission.CDTPlan.rot, Complex.norm_exp]
    have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h, Real.exp_zero]
  -- `rot (a + b) = rot a * rot b`
  have hrotadd : ∀ a b : ℝ,
      Submission.CDTPlan.rot (a + b) = Submission.CDTPlan.rot a * Submission.CDTPlan.rot b := by
    intro a b
    rw [Submission.CDTPlan.rot, Submission.CDTPlan.rot, Submission.CDTPlan.rot, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the circle bound `‖rot u - rot v‖ ≤ 2π|u - v|`
  have hsub : ‖Submission.CDTPlan.rot u - Submission.CDTPlan.rot v‖ ≤ 2 * Real.pi * |u - v| := by
    have hfac : Submission.CDTPlan.rot u - Submission.CDTPlan.rot v
        = Submission.CDTPlan.rot v * (Submission.CDTPlan.rot (u - v) - 1) := by
      rw [mul_sub, mul_one, ← hrotadd v (u - v), show v + (u - v) = u by ring]
    rw [hfac, norm_mul, hrot1 v, one_mul]
    have hx : Submission.CDTPlan.rot (u - v)
        = Complex.exp (Complex.I * ((2 * Real.pi * (u - v) : ℝ) : ℂ)) := by
      rw [Submission.CDTPlan.rot]
      congr 1
      push_cast
      ring
    rw [hx, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hsin := Real.abs_sin_le_abs (x := 2 * Real.pi * (u - v) / 2)
    calc 2 * |Real.sin (2 * Real.pi * (u - v) / 2)|
        ≤ 2 * |2 * Real.pi * (u - v) / 2| := by linarith [hsin]
      _ = 2 * Real.pi * |u - v| := by
          rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul, abs_mul,
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg Real.pi_pos.le]
          ring
  calc ‖Rr * Submission.CDTPlan.rot u - Rr * Submission.CDTPlan.rot v‖
      = ‖(Rr : ℂ) * (Submission.CDTPlan.rot u - Submission.CDTPlan.rot v)‖ := by rw [← mul_sub]
    _ = Rr * ‖Submission.CDTPlan.rot u - Submission.CDTPlan.rot v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
    _ ≤ Rr * (2 * Real.pi * |u - v|) := mul_le_mul_of_nonneg_left hsub hR
    _ = 2 * Real.pi * Rr * |u - v| := by ring

end Work.Cert.ACTrig
