import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- The diagonal element `α^t = diag(e^{t_i - (∑ t_j)/3})` is a group homomorphism in the
exponent: `aDiag (t + u) = aDiag t * aDiag u`. -/
theorem aDiag_add (t u : Fin 3 → ℝ) : aDiag (t + u) = aDiag t * aDiag u := by
  apply Subtype.ext
  change (Matrix.diagonal fun i => Real.exp ((t + u) i - (∑ j, (t + u) j) / 3)) =
    (Matrix.diagonal fun i => Real.exp (t i - (∑ j, t j) / 3)) *
    (Matrix.diagonal fun i => Real.exp (u i - (∑ j, u j) / 3))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

end Work.EKLC8Core
