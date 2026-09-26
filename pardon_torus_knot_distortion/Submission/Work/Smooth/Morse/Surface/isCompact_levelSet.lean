import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Surface.isCompact_torus

/-!
# Compactness of the level set `F ∩ {g = t}`

The surface `F = ψ(standard torus)` is compact (`Work.Smooth.Morse.Surface.isCompact_torus`) and
the level set `levelSet ψ g t` is a closed subset of it (it is `carrier ∩ {x | g x = t}`, the
intersection of the compact surface with the closed level set of a continuous function), hence
compact.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Surface

theorem isCompact_levelSet (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : Continuous g) (t : ℝ) : IsCompact (Work.Smooth.Morse.levelSet ψ g t) := by
  have hclosed : IsClosed (Work.Smooth.Morse.levelSet ψ g t) := by
    have h : Work.Smooth.Morse.levelSet ψ g t =
        (Work.Smooth.Morse.torus ψ).carrier ∩ {x : R3 | g x = t} := rfl
    rw [h]
    exact (isCompact_torus ψ).isClosed.inter (isClosed_eq hg continuous_const)
  exact IsCompact.of_isClosed_subset (isCompact_torus ψ) hclosed
    (Work.Smooth.Morse.levelSet_subset_carrier ψ g t)

end Work.Smooth.Morse.Surface
