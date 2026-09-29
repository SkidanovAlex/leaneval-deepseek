import Mathlib
import Submission.Work.TMComp.Defs
import Submission.Work.TMC16Core.Op.diagShift_spec

namespace Work.TMComp

/-- If `H`, `H'` are the Jacobi (shift-plus-diagonal) operators with coefficient
sequences `c`, `c'`, then `H - H'` is the diagonal operator with coefficients
`c - c'`; in particular its operator norm is bounded by any uniform bound `K` on
`‖c n - c' n‖`. -/
theorem norm_sub_le_of_coeffs {c c' : ℤ → ℂ} {K : ℝ} (hK : ∀ n, ‖c n - c' n‖ ≤ K)
    {H H' : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo}
    (h : Work.TMComp.IsJacobiOp c H) (h' : Work.TMComp.IsJacobiOp c' H') : ‖H - H'‖ ≤ K := by
  -- The diagonal operator with coefficients `c n - c' n`, whose norm is `≤ K`.
  obtain ⟨T, hT, hTK⟩ :=
    Work.TMC16Core.Op.diagShift_spec (fun n => c n - c' n) 0 K hK
  have heq : H - H' = T := by
    ext f n
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, h f n, h' f n, hT f n]
    rw [add_zero, sub_mul]
    abel
  rw [heq]
  exact hTK

end Work.TMComp
