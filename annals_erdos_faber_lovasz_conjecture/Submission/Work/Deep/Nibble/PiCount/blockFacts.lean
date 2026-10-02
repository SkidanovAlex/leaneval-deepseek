import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.KahnPartition

namespace Work.Deep.Nibble.PiCount

open Classical

/-- For a linear hypergraph whose edges through `v` have `r ≥ 2` vertices, the blocks `e ∖ {v}` of the edges through `v` all have `r - 1` elements, are pairwise disjoint, and avoid `v`. -/
theorem blockFacts {n : ℕ} {𝓗 : HG n} (v : Fin n) {r : ℕ} (hr : 2 ≤ r)
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hrsize : ∀ e ∈ 𝓗, v ∈ e → e.ncard = r) :
    (∀ e : {e : 𝓗 // v ∈ (e : Set (Fin n))},
        ((ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v).card = r - 1)
    ∧ (∀ e₁ e₂ : {e : 𝓗 // v ∈ (e : Set (Fin n))}, e₁ ≠ e₂ →
        Disjoint ((ErdosFaberLovaszConjecture.verts (e₁.1 : Set (Fin n))).erase v)
          ((ErdosFaberLovaszConjecture.verts (e₂.1 : Set (Fin n))).erase v))
    ∧ (v ∉ Finset.univ.biUnion (fun e : {e : 𝓗 // v ∈ (e : Set (Fin n))} =>
        (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v)) := by
  classical
  -- every edge through `v` spans exactly `r` vertices
  have hcard : ∀ e : {e : 𝓗 // v ∈ (e : Set (Fin n))},
      (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).card = r := by
    intro e
    have h : ErdosFaberLovaszConjecture.edgeSize (e.1 : Set (Fin n)) = r := by
      rw [ErdosFaberLovaszConjecture.edgeSize_eq_ncard]
      exact hrsize e.1.1 e.1.2 e.2
    simpa only [ErdosFaberLovaszConjecture.edgeSize] using h
  refine ⟨?_, ?_, ?_⟩
  · -- sizes: deleting `v` from a block leaves `r - 1` vertices
    intro e
    rw [Finset.card_erase_of_mem (by simpa using e.2), hcard e]
  · -- pairwise disjointness: two blocks can only meet in `v`, which is erased
    intro e₁ e₂ hne
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_erase] at ha1
    obtain ⟨hane, ha1'⟩ := ha1
    have hae1 : a ∈ (e₁.1.1 : Set (Fin n)) :=
      (ErdosFaberLovaszConjecture.mem_verts _ _).mp ha1'
    have hae2 : a ∈ (e₂.1.1 : Set (Fin n)) :=
      (ErdosFaberLovaszConjecture.mem_verts _ _).mp ((Finset.mem_erase.mp ha2).2)
    have hv1 : v ∈ (e₁.1.1 : Set (Fin n)) := e₁.2
    have hv2 : v ∈ (e₂.1.1 : Set (Fin n)) := e₂.2
    -- distinct edges of a linear hypergraph meet in at most one vertex
    have hval : e₁.1.1 ≠ e₂.1.1 := by
      intro h
      exact hne (Subtype.ext (Subtype.ext h))
    exact hane (hlin e₁.1.2 e₂.1.2 hval ⟨hae1, hae2⟩ ⟨hv1, hv2⟩)
  · -- every block has had `v` erased
    intro h
    rw [Finset.mem_biUnion] at h
    obtain ⟨e, -, he⟩ := h
    exact (Finset.mem_erase.mp he).1 rfl

end Work.Deep.Nibble.PiCount
