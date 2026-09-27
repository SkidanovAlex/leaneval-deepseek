import Mathlib
import Submission.Work.Endgame.Defs

namespace Work.Endgame

open scoped OnePoint

/-- The homeomorphism `onePointComplHomeomorph p : OnePoint ({p}ᶜ) ≃ₜ M` sends the point at
infinity to `p`: on the `OnePoint` side the map is `OnePoint.elim p Subtype.val`, so this is
`rfl` after unfolding the definition. -/
theorem onePointComplHomeomorph_apply_infty {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (p : M) : onePointComplHomeomorph p OnePoint.infty = p := by
  simp [onePointComplHomeomorph]

end Work.Endgame
