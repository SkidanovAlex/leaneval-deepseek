import Mathlib

namespace Work.RPV

/-- Reversing a chord flips the phase by `π`: if `z - w = ‖z - w‖ · e^{ia}`, then
`w - z = ‖w - z‖ · e^{i(a+π)}`. -/
theorem chordPS_phase_rev {z w : ℂ} {a : ℝ}
    (h : z - w = (‖z - w‖ : ℂ) * Complex.exp (a * Complex.I)) :
    w - z = (‖w - z‖ : ℂ) * Complex.exp ((a + Real.pi) * Complex.I) := by
  -- Splitting the phase sum and using `e^{iπ} = -1`.
  have hphase : Complex.exp (((a : ℂ) + (Real.pi : ℂ)) * Complex.I)
      = - Complex.exp ((a : ℂ) * Complex.I) := by
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  have hnorm : ((‖w - z‖ : ℝ) : ℂ) = ((‖z - w‖ : ℝ) : ℂ) := by rw [norm_sub_rev]
  rw [hphase, hnorm, mul_neg, ← h]
  ring

end Work.RPV
