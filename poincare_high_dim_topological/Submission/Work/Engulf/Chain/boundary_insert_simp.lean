import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Chain.ConeDefs

namespace Work.Engulf.Chain

/-- Distribute a union indexed by a finset over the insertion of one point:
`⋃_{v ∈ insert a s} f v = f a ∪ ⋃_{v ∈ s} f v`. -/
lemma biUnion_finset_insert {α β : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (f : α → Set β) :
    (⋃ v ∈ insert a s, f v) = f a ∪ ⋃ v ∈ s, f v := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
  constructor
  · rintro ⟨v, (rfl | hv), hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨v, hv, hx⟩
  · rintro (hx | ⟨v, hv, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨v, Or.inr hv, hx⟩

/-- The boundary of the simplex `insert a σ` is the union of the simplex on `σ` (the facet opposite
the apex `a`) with the lateral boundary `coneBd a σ = ⋃ w ∈ σ, simp ((insert a σ) \ {w})` of the
cone `aσ`: `⋃_{v ∈ insert a σ} simp ((insert a σ) \ {v}) = simp σ ∪ coneBd a σ`.  (`a ∉ σ` is
needed: `(insert a σ).erase a = σ`.) -/
theorem boundary_insert_simp {N : ℕ} (σ : Finset (PL.E N)) (a : PL.E N) (ha : a ∉ σ) :
    (⋃ v ∈ insert a σ, PL.simp ((insert a σ).erase v))
      = PL.simp σ ∪ Work.Engulf.Chain.coneBd a σ := by
  rw [coneBd, biUnion_finset_insert σ a (fun v => PL.simp ((insert a σ).erase v)),
    Finset.erase_insert ha]

end Work.Engulf.Chain
