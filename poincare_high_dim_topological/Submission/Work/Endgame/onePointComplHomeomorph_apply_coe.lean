import Mathlib
import Submission.Work.Endgame.Defs

namespace Work.Endgame

open scoped OnePoint

/-- The homeomorphism `onePointComplHomeomorph p : OnePoint ({p}ᶜ) ≃ₜ M` sends a point
`x : {p}ᶜ` (a point of `M` different from `p`, viewed in the one-point compactification)
to `x` itself: on the `OnePoint` side the map is `OnePoint.elim p Subtype.val`, so this is
`rfl` after unfolding the definition, exactly as in `onePointComplHomeomorph_apply_infty`. -/
theorem onePointComplHomeomorph_apply_coe {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (p : M) (x : ({p}ᶜ : Set M)) :
    onePointComplHomeomorph p (x : OnePoint ({p}ᶜ : Set M)) = (x : M) := by
  simp [onePointComplHomeomorph]

end Work.Endgame
