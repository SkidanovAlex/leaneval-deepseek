import Mathlib
import Submission.Work.RESOL.Resolution

namespace Work.RESOL

/-- Every term of the resolution `X` (defined from the atom cover) is a small atomic sum, i.e. a
small coproduct of free light condensed abelian groups `ℤ[S]` on light profinite sets `S`. -/
theorem isAtomicSum_X (M : LightCondAb) (n : ℕ) :
    Work.RESOL.IsAtomicSum ((Work.RESOL.X.obj M).X n) := by
  rcases n with _ | _ | n
  · -- degree `0`: the term is the atom cover `cov.obj M`
    exact isAtomicSum_of_iso (LR.chainComplexXZeroIso M).symm (isAtomicSum_cov M)
  · -- degree `1`: the term is the atom cover of the kernel of the augmentation
    exact isAtomicSum_of_iso (LR.chainComplexXOneIso M).symm (isAtomicSum_cov _)
  · -- degree `n + 2`: the term is the atom cover of the kernel of the differential
    exact isAtomicSum_of_iso (LR.chainComplexXIso M n).symm (isAtomicSum_cov _)

end Work.RESOL
