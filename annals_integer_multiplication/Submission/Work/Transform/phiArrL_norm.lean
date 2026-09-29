import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.psiFlatL_norm

namespace Work.Transform

/-- `T̃` (the blockwise multiplication by `ζ^c`) does not increase the sup norm. -/
theorem phiArrL_norm (r : ℕ) (ts' : List ℕ) (w : Fin ((ts' ++ [r]).prod) → ℂ) :
    ‖Work.Transform.phiArrL r ts' w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 (fun a => ?_)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun c => ?_)
  rw [phiArrL, norm_mul, norm_zeta, one_mul]
  exact norm_le_pi_norm w _

end Work.Transform
