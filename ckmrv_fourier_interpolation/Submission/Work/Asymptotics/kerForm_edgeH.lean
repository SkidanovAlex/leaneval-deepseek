import Mathlib
import Submission.Work.Asymptotics.kerFormDefs

namespace Work.Asymptotics

/-- The split `e^{iπr²(u+iv)} = e^{iπr²u}·e^{-πr²v}` of the exponential factor of the contour
integrand, i.e. `kerExp r (u + iv) = phaseWeight r u * gaussWeight r v`. -/
lemma kerExp_eq_phaseWeight_mul_gaussWeight (r u v : ℝ) :
    kerExp r ((u : ℂ) + (v : ℂ) * Complex.I)
      = phaseWeight r u * gaussWeight r v := by
  have hkey : (Real.pi : ℂ) * Complex.I * (r:ℂ)^2 * ((v:ℂ) * Complex.I)
      = -(Real.pi * r^2 * v : ℝ) := by
    rw [show (Real.pi : ℂ) * Complex.I * (r:ℂ)^2 * ((v:ℂ) * Complex.I)
        = (Real.pi : ℂ) * (r:ℂ)^2 * (v:ℂ) * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]
    push_cast
    ring
  rw [kerExp, phaseWeight, gaussWeight, ← Complex.exp_add]
  congr 1
  rw [mul_add, hkey]
  congr 1
  push_cast
  ring

/-- The horizontal edge integrand `edgeH` is the contour form `kerForm` evaluated at
`z = u + iv`: both are `K(τ,u+iv)·e^{iπr²(u+iv)}/i`. -/
theorem kerForm_edgeH (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane)
    (u v : ℝ) (hv : 0 < v) :
    Work.Asymptotics.edgeH ℓ d r τ u v
      = Work.Asymptotics.kerForm ℓ d r τ ((u : ℂ) + (v : ℂ) * Complex.I) := by
  rw [edgeH, kerForm, ofReImT_eq_ofComplex u v hv, kerExp_eq_phaseWeight_mul_gaussWeight]

end Work.Asymptotics
