import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Rigidity.SigmaEntryBound.sigmaR_entry_bound

namespace Work.Asymptotics

/-- The matrix entries of the paper's six-dimensional representation `σ` grow at most
polynomially in the Frobenius norm `Work.Asymptotics.Frob` of the group element.  This is
CKMRV Lemma `lem:polynomiallybounded` for `σ`, in the form used by the propagation
argument. -/
theorem sigma_entry_bound :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ i j : Fin 6,
      ‖(Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) γ)) i j‖
        ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N :=
  Work.Rigidity.SigmaEntryBound.sigmaR_entry_bound

end Work.Asymptotics
