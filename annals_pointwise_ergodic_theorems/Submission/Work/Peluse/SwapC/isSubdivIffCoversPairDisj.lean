import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

/-!
# `IsSubdiv` = `Covers` ∧ `PairDisj`

`IsSubdiv Λ` says that every `x : Fin s → Bool` lies in the cell of a **unique** leaf of `Λ`,
i.e. `∀ x, ∃! l, l ∈ Λ ∧ Agree x l`.  `Covers Λ` is the existence half of this statement and
`PairDisj Λ` is exactly its uniqueness half (two leaves whose cells meet are equal).  So the two
are equivalent by pure unfolding of the three definitions.
-/

/-- Unfolding form: `IsSubdiv Λ` is the conjunction of existence and uniqueness of the leaf whose
cell contains `x`, for every `x`. -/
theorem isSubdiv_iff_forall_existsUnique {s : ℕ} {Λ : List (CLeaf s)} :
    IsSubdiv Λ ↔ ∀ x : Fin s → Bool, ∃! l : CLeaf s, l ∈ Λ ∧ Agree x l :=
  Iff.rfl

theorem isSubdivIffCoversPairDisj {s : ℕ} {Λ : List (Work.Peluse.SwapC.CLeaf s)} :
    Work.Peluse.SwapC.IsSubdiv Λ ↔ Work.Peluse.SwapC.Covers Λ ∧ Work.Peluse.SwapC.PairDisj Λ := by
  refine ⟨fun h => ⟨?_, pairDisj_of_isSubdiv h⟩, ?_⟩
  · -- `Covers`: drop the uniqueness component of the `∃!`
    intro x
    obtain ⟨l, hl, _⟩ := h x
    exact ⟨l, hl⟩
  · -- `Covers ∧ PairDisj` reassembles the `∃!`: existence from `Covers`, uniqueness from
    -- `PairDisj` (the common point `x` is exactly a witness that the two cells meet).
    rintro ⟨hc, hpd⟩ x
    obtain ⟨l, hl, hx⟩ := hc x
    exact ⟨l, ⟨hl, hx⟩, fun l' ⟨hl', hx'⟩ => hpd l' hl' l hl ⟨x, hx', hx⟩⟩

end Work.Peluse.SwapC
