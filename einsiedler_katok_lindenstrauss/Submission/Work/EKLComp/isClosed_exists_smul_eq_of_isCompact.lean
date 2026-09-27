import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.X3Background

/-!
# Closedness of the "`K`-orbit" relation on `X₃ × X₃`

For a compact subset `K ⊆ SL₃(ℝ)` the set of pairs `(x, y) ∈ X₃ × X₃` such that `y = g • x` for
some `g ∈ K` is closed.

The proof is the standard compactness argument: on the compact space `↥K × (X₃ × X₃)` the locus
`{(g, x, y) | g • x = y}` is closed (preimage of the diagonal under a continuous map), and it is
mapped onto the set in question by the projection `↥K × (X₃ × X₃) → X₃ × X₃`, which is a closed map
because `↥K` is compact.
-/

set_option linter.style.haveILetI false

namespace Work.EKLComp

open Work.EKLContract

/-- If `K ⊆ SL₃(ℝ)` is compact, then the set of pairs `(x, y) ∈ X₃ × X₃` with `g • x = y` for some
`g ∈ K` is closed. -/
theorem isClosed_exists_smul_eq_of_isCompact (K : Set Work.EKLContract.SL3) (hK : IsCompact K) : IsClosed {p : Work.EKLContract.X3 × Work.EKLContract.X3 | ∃ g ∈ K, g • p.1 = p.2} := by
  -- `K`, as a subspace, is compact.
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  -- The "graph" of the action over `K` is closed in `↥K × (X₃ × X₃)`: it is the preimage of the
  -- diagonal under the continuous map `(g, x, y) ↦ (g • x, y)`.
  have hA : IsClosed {q : ↥K × (X3 × X3) | (q.1 : SL3) • q.2.1 = q.2.2} := by
    apply isClosed_eq
    · exact continuous_smul.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
    · exact continuous_snd.comp continuous_snd
  -- Projecting the first coordinate away is a closed map, as `↥K` is compact.
  have himg : Prod.snd '' {q : ↥K × (X3 × X3) | (q.1 : SL3) • q.2.1 = q.2.2}
      = {p : X3 × X3 | ∃ g ∈ K, g • p.1 = p.2} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.1, q.1.2, hq⟩
    · rintro ⟨g, hg, hgx⟩
      exact ⟨(⟨g, hg⟩, p), hgx, rfl⟩
  rw [← himg]
  exact isClosedMap_snd_of_compactSpace _ hA

end Work.EKLComp
