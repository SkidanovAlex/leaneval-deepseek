import Mathlib
import Submission.Work.TMComp.Defs
import Submission.Work.TMC16Core.Op.diagShift_spec

namespace Work.TMComp

/-- Every bounded coefficient sequence gives rise to a bounded "Jacobi" operator on
`ℓ²(ℤ)` with the coordinate formula `(H u) n = u (n + 1) + u (n - 1) + c n * u n`.

The operator is exhibited as the sum of three diagonal-times-shift operators:
the forward shift (`k = 1`, coefficient `1`), the backward shift (`k = -1`,
coefficient `1`) and the diagonal multiplication by `c` (`k = 0`), each of which
is produced by `Work.TMC16Core.Op.diagShift_spec`. -/
theorem exists_of_coeffs (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n, ‖c n‖ ≤ K) :
    ∃ H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo,
      Work.TMComp.IsJacobiOp c H := by
  obtain ⟨Tp, hTp, _⟩ :=
    Work.TMC16Core.Op.diagShift_spec (fun _ : ℤ => (1 : ℂ)) 1 1 (fun n => by simp)
  obtain ⟨Tm, hTm, _⟩ :=
    Work.TMC16Core.Op.diagShift_spec (fun _ : ℤ => (1 : ℂ)) (-1) 1 (fun n => by simp)
  obtain ⟨Td, hTd, _⟩ := Work.TMC16Core.Op.diagShift_spec c 0 K hK
  refine ⟨Tp + Tm + Td, ?_⟩
  intro u n
  have h1 : Tp u n = u (n + 1) := by rw [hTp]; simp
  have h2 : Tm u n = u (n - 1) := by
    rw [hTm]
    simp only [one_mul]
    ring_nf
  have h3 : Td u n = c n * u n := by
    rw [hTd]
    ring_nf
  simp [add_apply, h1, h2, h3]

end Work.TMComp
