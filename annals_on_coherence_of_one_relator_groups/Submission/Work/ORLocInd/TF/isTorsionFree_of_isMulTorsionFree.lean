import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.TF

/-- `IsMulTorsionFree` (all power maps `x ↦ x ^ n`, `n ≠ 0`, are injective) implies
`Work.ORLocInd.IsTorsionFree` (the only element of finite order is the identity):
if `g ^ n = 1` with `n ≠ 0`, then also `1 ^ n = 1`, and injectivity of `· ^ n` gives `g = 1`. -/
theorem isTorsionFree_of_isMulTorsionFree {G : Type*} [Group G] [IsMulTorsionFree G] :
    Work.ORLocInd.IsTorsionFree G := by
  intro g hg
  exact hg.eq_one'

end Work.ORLocInd.TF
