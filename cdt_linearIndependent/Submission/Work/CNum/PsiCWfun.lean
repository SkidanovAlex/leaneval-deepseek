import Mathlib
import Submission.Work.CNum.Basic

namespace Work.CNum

/-- Fix `c = 23/10`, `R(z) = (1+c²)²(1+z)² - 16c²z` and recall
`psiC = -(3/4)·lune(23/10)`, `lune(c,z) = (z(1+c²) - 1 - c² + R(z)^{1/2})/(2(c²-1))`,
`Wfun z = -(((1+c²)(z-1) + √R(z))/d)` with `d = 2(c²-1)`.

The two expressions differ only by the identification of the principal square
root `√R(z) = R(z) ^ (1/2 : ℂ)` (which is a definitional unfolding, since
`Complex.sqrt a = a ^ (2⁻¹ : ℂ)`), and by the elementary rearrangement
`z(1+c²) - 1 - c² = (1+c²)(z-1)`. Hence `psiC = (3/4)·Wfun`. -/
theorem PsiCWfun (z : ℂ) : Submission.CDTPlan.psiC z = (3 / 4 : ℂ) * Work.CNum.Wfun z := by
  rw [Submission.CDTPlan.psiC, Work.CNum.Wfun]
  -- `Complex.sqrt a = a ^ (2⁻¹ : ℂ)`, and `(2⁻¹ : ℂ) = 1/2`.
  have hsq : Complex.sqrt (Work.CNum.Ra z) = (Work.CNum.Ra z) ^ (1 / 2 : ℂ) := by
    rw [Complex.sqrt, show (2 : ℂ)⁻¹ = (1 / 2 : ℂ) by norm_num]
  rw [hsq, Work.CNum.Ra, Work.CNum.AR, Work.CNum.BR, Work.CNum.dR, Work.CNum.cR,
    Submission.CDTPlan.lune]
  norm_num
  ring

end Work.CNum
