import Mathlib
import Submission.Work.Pert.Setup

namespace Work.Pert

theorem norm_one_sub_exp_pole_witness {α : ℂ} (hα : α ≠ 0) :
    ‖(1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * (((-15 / 16 : ℝ) : ℂ) / α)))‖
      = 2 * Real.sin (Real.pi / 16) := by
  -- α ≠ 0, so the exponent collapses to I * (15π/8).
  have hexp : -(2 * (Real.pi : ℂ) * Complex.I * α * (((-15 / 16 : ℝ) : ℂ) / α))
      = Complex.I * ((15 / 8 * Real.pi : ℝ) : ℂ) := by
    field_simp
    push_cast
    ring
  rw [norm_sub_rev, hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
  -- sin(15π/16) = sin(π/16)
  have hx : Real.sin (15 / 8 * Real.pi / 2) = Real.sin (Real.pi / 16) := by
    have h1 : 15 / 8 * Real.pi / 2 = Real.pi - Real.pi / 16 := by ring
    rw [h1, Real.sin_pi_sub]
  rw [hx]
  have hpos : 0 < Real.sin (Real.pi / 16) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  rw [Real.norm_of_nonneg (by linarith)]

end Work.Pert
