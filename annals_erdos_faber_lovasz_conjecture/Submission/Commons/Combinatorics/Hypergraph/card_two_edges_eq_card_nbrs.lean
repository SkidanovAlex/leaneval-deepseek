import Mathlib.Data.Set.Card

namespace Commons.Combinatorics.Hypergraph

/-- If `s` has exactly two elements and `w ∈ s`, then `s = {w, x}` for some `x`. -/
private lemma eq_pair_of_ncard_two_of_mem {α : Type*} {s : Set α} {w : α}
    (hs : s.ncard = 2) (hw : w ∈ s) : ∃ x, s = ({w, x} : Set α) := by
  obtain ⟨y, z, hyz, rfl⟩ := Set.ncard_eq_two.mp hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with hwy | hwz
  · exact ⟨z, by rw [hwy]⟩
  · exact ⟨y, by rw [hwz]; exact Set.pair_comm y z⟩

/-- The map `x ↦ {w, x}` on `Fin n` is injective. -/
private lemma injective_pair {n : ℕ} (w : Fin n) :
    Function.Injective (fun x : Fin n => ({w, x} : Set (Fin n))) := by
  intro x1 x2 h
  rw [Set.pair_eq_pair_iff] at h
  rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact h2.trans h1

/-- For a family `R` of 2-element subsets of `Fin n` and a vertex `w`, the
number of edges of `R` containing `w` equals the number of vertices `x` with
`{w,x} ∈ R` (the map `e ↦ e \ {w}` is a bijection). -/
theorem card_two_edges_eq_card_nbrs {n : ℕ} (R : Set (Set (Fin n)))
    (hR : ∀ e ∈ R, e.ncard = 2) (w : Fin n) :
    {e ∈ R | w ∈ e}.ncard = {x : Fin n | ({w, x} : Set (Fin n)) ∈ R}.ncard := by
  classical
  have hinj : Function.Injective (fun x : Fin n => ({w, x} : Set (Fin n))) :=
    injective_pair w
  have himage :
      (fun x : Fin n => ({w, x} : Set (Fin n))) '' {x : Fin n | ({w, x} : Set (Fin n)) ∈ R}
        = {e ∈ R | w ∈ e} := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, by simp⟩
    · rintro ⟨heR, hwe⟩
      obtain ⟨x, hx⟩ := eq_pair_of_ncard_two_of_mem (hR e heR) hwe
      refine ⟨x, ?_, ?_⟩
      · show ({w, x} : Set (Fin n)) ∈ R
        rw [← hx]; exact heR
      · exact hx.symm
  rw [← himage]
  exact Set.ncard_image_of_injective _ hinj

end Commons.Combinatorics.Hypergraph