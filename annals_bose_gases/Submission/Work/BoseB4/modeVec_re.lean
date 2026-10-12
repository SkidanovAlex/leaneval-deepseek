import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- The real part of the localised plane wave `modeVec ℓ k = e^{ik·x} χ_Λ`:
this is `χ_Λ(x) · cos⟪k,x⟫`, since `Re e^{i t} = cos t` and `χ_Λ` is real. -/
theorem modeVec_re (B : Work.BoseB4.BoxData) (ℓ : ℝ) (k x : EuclideanSpace ℝ (Fin 3)) :
    (B.modeVec ℓ k x).re = B.chiLam ℓ x * Real.cos (inner ℝ k x) := by
  rw [BoxData.modeVec_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, Real.exp_zero,
    one_mul]
  ring_nf

end Work.BoseB4
