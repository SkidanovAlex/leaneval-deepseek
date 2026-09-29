import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

open HvdH

/-- The Bluestein chirp has modulus `1`. -/
theorem chirp_norm (ts : List ℕ) (j : ℕ) : ‖Work.Transform.chirp ts j‖ = 1 := by
  rw [chirp, Complex.norm_exp]
  have h : (Real.pi * Complex.I * (phase ts (digits ts j) (digits ts j) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

end Work.Transform
