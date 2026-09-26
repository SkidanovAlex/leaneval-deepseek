import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Surface.isCompact_torus

/-!
# Compactness of the closed sublevel region `F ∩ {g ≤ t}`

The surface `F = ψ(standard torus)` is compact (`Work.Smooth.Morse.Surface.isCompact_torus`) and
the closed region `closedRegion ψ g t` is the trace on it of the closed sublevel set
`{x | g x ≤ t}` of the continuous function `g`:

`closedRegion ψ g t = (torus ψ).carrier ∩ {x : ℝ³ | g x ≤ t}`.

It is therefore a closed subset of the compact surface, hence compact.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Surface

theorem isCompact_closedRegion (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : Continuous g) (t : ℝ) : IsCompact (Work.Smooth.Morse.closedRegion ψ g t) := by
  have hclosed : IsClosed (Work.Smooth.Morse.closedRegion ψ g t) := by
    have h : Work.Smooth.Morse.closedRegion ψ g t =
        (Work.Smooth.Morse.torus ψ).carrier ∩ {x : R3 | g x ≤ t} := rfl
    rw [h]
    exact (isCompact_torus ψ).isClosed.inter (isClosed_le hg continuous_const)
  exact IsCompact.of_isClosed_subset (isCompact_torus ψ) hclosed
    (Work.Smooth.Morse.closedRegion_subset_carrier ψ g t)

end Work.Smooth.Morse.Surface
