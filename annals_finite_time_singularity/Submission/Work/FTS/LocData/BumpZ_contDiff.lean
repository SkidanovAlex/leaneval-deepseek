import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The radial factor `bumpZ z = χ(4z - 5)` of the bump is `C^∞` on all of `ℝ`: it is the
composition of the globally `C^∞` cut-off `χ` (`Work.Stability.chi_contDiff`) with the affine
map `z ↦ 4z - 5`. -/
theorem BumpZ_contDiff : ContDiff ℝ (⊤ : ℕ∞) Work.FTS.LocData.bumpZ := by
  unfold bumpZ
  exact Work.Stability.chi_contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

end Work.FTS.LocData
