import Mathlib
import Submission.Work.Smooth.Jordan.Separation

/-!
# A preconnected set lies on one side of a Jordan curve

The complement of the trace of a simple closed curve is, by `PlaneSeparation`, the disjoint union
of two open sets `U` (outside) and `V` (inside).  Any preconnected subset of that complement must
therefore be contained in one of the two sides: it cannot meet both `U` and `V` without meeting
their (empty) intersection.  This is the elementary topological fact
`IsPreconnected.subset_or_subset` of Mathlib, specialised to a `PlaneSeparation` datum.
-/

namespace Work.Smooth.Jordan

/-- **A preconnected subset of the complement of a Jordan curve lies on one side.**  If `W` is
preconnected and disjoint from the trace of `c`, then `W` is contained in the outside `h.U` or in
the inside `h.V`. -/
theorem plane_separation_preconnected_subset {c : PlaneCurve} (h : PlaneSeparation c) {W : Set ℂ}
    (hW : IsPreconnected W) (hsub : W ⊆ c.traceᶜ) : W ⊆ h.U ∨ W ⊆ h.V :=
  hW.subset_or_subset h.isOpen_U h.isOpen_V h.disjoint_UV
    (hsub.trans (le_of_eq h.union_eq.symm))

end Work.Smooth.Jordan
