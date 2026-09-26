import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Asymptotics.CarryBoundBlock
import Submission.Work.Asymptotics.block_factorization
import Submission.Work.Asymptotics.CarryBoundBlockZ
import Submission.Work.Asymptotics.CarryBoundGlobal

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

/-- **The carries of the reduction of a group element modulo `𝓘` are polynomially bounded.**
For every `γ ∈ SL(2,ℤ)` the error term `γ - Σ_j σ(γ)_{0j} M6_j` of the reduction of `γ` modulo
the right ideal `Kernels.IdealI ⊔ (z-1)R` (where `z = Rneg = -I`) can be written as
`(T-1)²a + S(T-1)²b + (z-1)c` with `a, b, c ∈ R` whose `ℓ¹`-norms and whose supports
(measured in the Frobenius norm) are at most `C (1 + Frob γ)^N`.  This is CKMRV Lemma
`lem:cocyclebounds` for the first row `i = 0`, with the `(z-1)`-summand that the ideal
`Work.Residues.idealI` genuinely needs (cf. the `γ = -I` case). -/
theorem carry_bound :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ a b c : Work.Kernels.R,
      (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) γ -
        ∑ j, (Work.Residues.sigmaR
              (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) γ)) 0 j
              • Work.Residues.M6 j
          = (Work.Kernels.R_T - 1) ^ 2 * a + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * b
            + (Work.Residues.Rneg - 1) * c)
      ∧ Work.Asymptotics.coeffNorm a ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
      ∧ Work.Asymptotics.coeffNorm b ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
      ∧ Work.Asymptotics.coeffNorm c ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N
      ∧ Work.Asymptotics.supportFrobLe a (C * (1 + Work.Asymptotics.Frob γ) ^ N)
      ∧ Work.Asymptotics.supportFrobLe b (C * (1 + Work.Asymptotics.Frob γ) ^ N)
      ∧ Work.Asymptotics.supportFrobLe c (C * (1 + Work.Asymptotics.Frob γ) ^ N) := by
  obtain ⟨C, N, hC, hN, hmain⟩ := carry_bound_aux
  refine ⟨C, N, hC, hN, fun γ => ?_⟩
  obtain ⟨t, ht, hCB⟩ := hmain γ
  refine ⟨t.1, t.2.1, t.2.2, ?_, hCB.1, hCB.2.1, hCB.2.2.1,
    hCB.2.2.2.1, hCB.2.2.2.2.1, hCB.2.2.2.2.2⟩
  have h1 : Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) γ) 0
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) γ
        - ∑ j, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) γ)) 0 j
            • Work.Residues.M6 j := by
    rw [Work.Residues.rowDiff, Work.Residues.M6_zero, one_mul]
  rw [← ht.trans h1]
  rfl

end Work.Asymptotics
