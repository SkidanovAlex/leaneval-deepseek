import Submission.Work.Step2.Geometry
import Submission.Work.Step2.halfAbove_eq_frontier_upperBody

/-!
# The two halves of the double bubble bound the two half-boxes

The geometric endpoint identity of the reduction: the half `H₁` of Pardon's double bubble is the
boundary of the upper half-*box* (`halfAbove = frontier (upperBody)`), and conversely the closed
upper half-box is the upper half-box together with `H₁`.  Hence the region of the surface inside
`H₁` is the crux's upper half-region (`Geometry.upperRegion_eq_carrier_upperBody`), so Pardon's
"the region inside one of the two half-spheres" is literally `upperRegion`/`lowerRegion`.

The frontier identity itself is proved in `Submission/Work/Step2/halfAbove_eq_frontier_upperBody.lean`
(`Work.Step2.halfAbove_eq_frontier_upperBody`), under the two hypotheses `0 < s` and
`|u| < boxSide 2 * s` which say that the cutting plane meets the interior of the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

/-- **The closed upper half-box is the upper half-box together with the half `H₁` of the double
bubble.** -/
theorem closure_upperBody_eq {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    closure (upperBody s c σ u) = upperBody s c σ u ∪ halfAbove s c σ u := by
  rw [halfAbove_eq_frontier_upperBody hs c σ hu, closure_eq_interior_union_frontier,
    (isOpen_upperBody (s := s) (c := c) (σ := σ) (u := u)).interior_eq]

end

end Work.Step2
