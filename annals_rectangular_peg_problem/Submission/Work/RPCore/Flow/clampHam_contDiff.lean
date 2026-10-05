import Mathlib
import Submission.Work.RPCore.Flow.HamFlow

namespace Work.RPCore.Flow

/-- The time-clamped Hamiltonian `clampHam Hh t = H (clampPsi t) ·` is `C²` in the space
variable: the full `C⁴` smoothness of `Hh.smooth : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)`
composed with the constant-in-`x` slice map `x ↦ (clampPsi t, x)`. -/
theorem clampHam_contDiff (Hh : Work.RPV.CptPerHam) (t : ℝ) :
    ContDiff ℝ 2 (Work.RPCore.clampHam Hh t) := by
  have h : ContDiff ℝ 4 (fun x : Work.RPV.PS => Hh.H (Work.RPCore.clampPsi t) x) :=
    Hh.smooth.comp (contDiff_const.prodMk contDiff_id)
  exact h.of_le (by norm_num)

end Work.RPCore.Flow
