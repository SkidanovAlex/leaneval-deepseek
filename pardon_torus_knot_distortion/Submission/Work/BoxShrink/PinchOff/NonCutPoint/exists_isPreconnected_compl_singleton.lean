import Mathlib
import Submission.Work.BoxShrink.PinchOff.NonCutPoint.Basic
import Submission.Work.BoxShrink.PinchOff.NonCutPoint.Main

/-!
# Existence of a non-cut point in a compact connected `T2` space

This is the `T2Space` form of the non-cut point theorem proved (for `T1Space`) in
`Submission.Work.BoxShrink.PinchOff.NonCutPoint.Main`.  Since `T2Space` refines `T1Space`, the
theorem there applies verbatim.
-/

namespace Work.BoxShrink.PinchOff.NonCutPoint

/-- **Existence of a non-cut point.**  A nonempty compact connected Hausdorff space `X` has a
point `x` whose removal leaves a preconnected space: `X \ {x}` is preconnected. -/
theorem exists_isPreconnected_compl_singleton (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [Nonempty X] (hX : IsPreconnected (Set.univ : Set X)) :
    ∃ x : X, IsPreconnected (Set.compl {x}) :=
  Work.BoxShrink.PinchOff.exists_isPreconnected_compl_singleton_of_compact (X := X) hX

end Work.BoxShrink.PinchOff.NonCutPoint
