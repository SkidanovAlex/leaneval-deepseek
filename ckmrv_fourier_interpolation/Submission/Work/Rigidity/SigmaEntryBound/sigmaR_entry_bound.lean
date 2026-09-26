import Mathlib
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Slash
import Submission.Work.Rigidity.SigmaEntryBound.Defs
import Submission.Work.Rigidity.SigmaEntryBound.Expansion
import Submission.Work.Rigidity.SigmaEntryBound.StepAux
import Submission.Work.Rigidity.SigmaEntryBound.Assembly

namespace Work.Rigidity.SigmaEntryBound

open scoped MatrixGroups MonoidAlgebra

/-- **CKMRV, Lemma `lem:polynomiallybounded`, for the representation `σ`.**  The matrix entries
of `σ_R(γ)` grow at most polynomially in the Frobenius norm of `γ`.  The proof combines the
continued fraction expansion of `γ` (`Expansion.lean`), the explicit quartic growth of the
powers of `σ(T)` and `σ(T)⁻¹` (`sigmaT_pow_bound`) and the submultiplicativity of the squared
Frobenius norm (`frob2C_mul`). -/
theorem sigmaR_entry_bound :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ i j : Fin 6,
      ‖(Work.Residues.sigmaR (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) γ)) i j‖
        ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N := by
  obtain ⟨C0, N0, hC0, hN0, h⟩ := frob2C_W_bound
  refine ⟨1 + C0, N0, by linarith, hN0, ?_⟩
  intro γ i j
  have h1 : ‖(W γ) i j‖ ≤ 1 + frob2C (W γ) := frob2C_entry_le (W γ) i j
  have h2 : frob2C (W γ) ≤ C0 * (1 + Work.Asymptotics.Frob γ) ^ N0 := h γ
  have hF1 : (1 : ℝ) ≤ 1 + Work.Asymptotics.Frob γ := by
    have := Work.Asymptotics.Frob_nonneg γ
    linarith
  have h3 : (1 : ℝ) ≤ (1 + Work.Asymptotics.Frob γ) ^ N0 := Real.one_le_rpow hF1 hN0
  calc ‖(W γ) i j‖ ≤ 1 + frob2C (W γ) := h1
    _ ≤ 1 + C0 * (1 + Work.Asymptotics.Frob γ) ^ N0 := by linarith
    _ ≤ (1 + C0) * (1 + Work.Asymptotics.Frob γ) ^ N0 := by nlinarith [h3, hC0]

end Work.Rigidity.SigmaEntryBound
