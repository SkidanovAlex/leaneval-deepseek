import Mathlib
import Submission.Work.RPB.B1.PolarDefs

namespace Work.RPB.B1

/-- For a point `p = (r, φ)` with `r ≠ 0`, the polar-coordinate value `polarCoord.symm p` equals
`r · e^{iφ}`; hence dividing by it and multiplying by `r` recovers the factor `e^{-iφ}`. -/
theorem polar_symm_eq (p : ℝ × ℝ) :
    (Complex.polarCoord.symm p : ℂ) = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

/-- Pointwise polar identity: multiplying the imaginary part of `C / polarCoord.symm p` by the
radius `p.1` removes the radial factor, leaving the imaginary part of `C · e^{-i p.2}`. -/
theorem polar_pointwise (C : ℂ) (p : ℝ × ℝ) (hp : p.1 ≠ 0) : p.1 * ((C / (Complex.polarCoord.symm p : ℂ)).im) = (C * Complex.exp (-(p.2 : ℂ) * Complex.I)).im := by
  rw [polar_symm_eq]
  have hneg : -(p.2 : ℂ) * Complex.I = -((p.2 : ℂ) * Complex.I) := by ring
  have hid : (p.1 : ℂ) * (C / ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)))
      = C * Complex.exp (-((p.2 : ℂ) * Complex.I)) := by
    have h1 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp
    have h2 : Complex.exp ((p.2 : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [mul_assoc, ← Complex.exp_add]
    simp
  calc p.1 * ((C / ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))).im)
      = (((p.1 : ℂ) * (C / ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))))).im := by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    _ = (C * Complex.exp (-((p.2 : ℂ) * Complex.I))).im := by rw [hid]
    _ = (C * Complex.exp (-(p.2 : ℂ) * Complex.I)).im := by rw [hneg]

end Work.RPB.B1
