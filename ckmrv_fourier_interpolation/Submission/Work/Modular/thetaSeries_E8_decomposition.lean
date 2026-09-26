import Mathlib
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.E8ThetaAux
import Submission.Work.Modular.thetaSeries_E8_S_smul

namespace Work.Modular

/-- The decomposition of the `E₈` theta series into eighth powers of the Jacobi theta
functions, in the normalisation of `Submission.Work.Modular.ThetaFuncs`:
`θ₃ = jacobiTheta`, `θ₄ = jacobiTheta₂ (1/2) ·` and `θ₂ = exp (π i τ / 4) · jacobiTheta₂ (τ/2) ·`.

This is the restatement of `Work.Modular.thetaSeries_E8_decomp`, whose `Th3`, `Th4`, `Th2`
are by definition the same three functions. -/
theorem thetaSeries_E8_decomposition (τ : UpperHalfPlane) :
    Work.Modular.thetaSeries Work.Modular.E8 τ =
      (1 / 2) * (Work.Modular.theta3 τ ^ 8 + Work.Modular.theta4 τ ^ 8 +
        Work.Modular.theta2 τ ^ 8) := by
  rw [thetaSeries_E8_decomp τ, Th3, Th4, Th2, theta3, theta4, theta2]

end Work.Modular
