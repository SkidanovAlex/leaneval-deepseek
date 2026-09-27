import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.onePointComplHomeomorph_apply_infty

namespace Work.Endgame

open scoped OnePoint

/-- The inverse of `onePointComplHomeomorph p : OnePoint ({p}ᶜ) ≃ₜ M` sends `p` to the point at
infinity, since `onePointComplHomeomorph p` sends `∞` to `p`
(`onePointComplHomeomorph_apply_infty`). -/
theorem onePointComplHomeomorph_symm_apply_self {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (p : M) : (onePointComplHomeomorph p).symm p = OnePoint.infty := by
  rw [Homeomorph.symm_apply_eq]
  exact onePointComplHomeomorph_apply_infty p

end Work.Endgame
