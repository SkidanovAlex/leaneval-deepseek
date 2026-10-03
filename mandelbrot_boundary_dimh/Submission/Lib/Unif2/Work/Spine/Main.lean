import Submission.Lib.Unif2.Work.Spine.Spine

/-!
# `Work.Spine.Main` — the deliverable of the subproject

Two theorems, in namespace `Work.Spine`:

* `isFreeGroup_fundamentalGroup_of_noncompact`: `π₁` of a connected second countable non-compact
  Riemann surface is free (Johansson/Stallings);
* `simplyConnectedSpace_of_subsingleton_hom_toReal`: Hubbard Theorem 1.1.2's topological step — a
  connected non-compact Riemann surface with no non-trivial homomorphism `π₁ → ℝ` is simply
  connected.

Both are immediately reduced (in `Submission/Work/Spine/Spine.lean`) to the single geometric input
`Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact` — the spine theorem of
Johansson/Stallings — and to the assembly layer in `Submission/Work/Spine/Basic.lean`.
-/

namespace Work.Spine

end Work.Spine
