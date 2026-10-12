import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseRowsFS.RowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem kmomLabNormGe {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) (hk : k ≠ 0) :
    2 * Real.pi / ℓ ≤ ‖Work.BoseBoxFock.kmomLab ℓ N k‖ := by
  have hlab : Work.BoseBoxFock.labVec N k ≠ 0 := by
    intro h
    refine hk (funext fun i => (ZMod.valMinAbs_eq_zero (k i)).mp ?_)
    have := congrFun h i
    simpa only [Work.BoseBoxFock.labVec, Pi.zero_apply] using this
  calc 2 * Real.pi / ℓ = 2 * Real.pi / ℓ * 1 := (mul_one _).symm
    _ ≤ 2 * Real.pi / ℓ * ‖Work.BoseRowsFS.vecZ (Work.BoseBoxFock.labVec N k)‖ :=
        mul_le_mul_of_nonneg_left (Work.BoseRowsFS.norm_vecZ_ge_one hlab) (by positivity)
    _ = ‖Work.BoseBoxFock.kmomLab ℓ N k‖ := (Work.BoseRowsFS.norm_kmomLab hℓ N k).symm

end Work.BoseFixR
