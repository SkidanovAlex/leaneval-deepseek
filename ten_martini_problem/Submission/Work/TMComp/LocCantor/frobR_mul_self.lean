import Mathlib
import Submission.Work.TMComp.LocCantor.frobR_defs
import Submission.Work.TMComp.LocCantor.sl2_fin2_mul_self
import Submission.Work.TMComp.LocCantor.sqsum_smul_sub

namespace Work.TMComp.LocCantor

/-- The Frobenius norm of the square of an `SL₂(ℝ)` matrix, in real form:
`‖B²‖_F² = 2 + (tr B)² (‖B‖_F² - 2)`.

Since `B² = tr(B) · B - 1` (Cayley–Hamilton, `sl2_fin2_mul_self`), the sum of the squares
of the entries of `B²` equals `t² · Σ Bᵢⱼ² - 2 t · tr B + 2` with `t = tr B`
(`sqsum_smul_sub`), which rearranges to the stated identity. -/
theorem frobR_mul_self (B : Matrix (Fin 2) (Fin 2) ℝ) (hdet : B.det = 1) :
    Work.TMComp.LocCantor.frobR (B * B) ^ 2 = 2 + B.trace ^ 2 * (Work.TMComp.LocCantor.frobR B ^ 2 - 2) := by
  have hsq : B * B = B.trace • B - (1 : ℝ) • 1 := by
    simpa using sl2_fin2_mul_self B hdet
  rw [frobR_sq (B * B), hsq, sqsum_smul_sub B B.trace 1, frobR_sq B]
  ring

end Work.TMComp.LocCantor
