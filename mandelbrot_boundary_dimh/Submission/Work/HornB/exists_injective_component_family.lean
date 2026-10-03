import Mathlib

namespace Work.HornB

/-- If the connected components (inside `P`) of the points of `P` do not fit in any
finite collection, then there is an injective family of maximal preconnected subsets
of `P` (namely, an enumeration of infinitely many distinct components). -/
theorem exists_injective_component_family {P : Set ℂ}
    (h : ¬ ∃ s : Finset (Set ℂ), ∀ z ∈ P, connectedComponentIn P z ∈ s) :
    ∃ f : ℕ → Set ℂ, Function.Injective f ∧
      (∀ k : ℕ, f k ⊆ P) ∧ (∀ k : ℕ, IsPreconnected (f k)) ∧
      (∀ (k : ℕ) (C : Set ℂ), IsPreconnected C → C ⊆ P → (f k ∩ C).Nonempty → C ⊆ f k) := by
  classical
  -- the set of all connected components of points of `P`
  set S : Set (Set ℂ) := {K | ∃ z ∈ P, K = connectedComponentIn P z} with hSdef
  -- the hypothesis says exactly that `S` is infinite
  have hSinf : S.Infinite := by
    intro hf
    refine h ⟨hf.toFinset, ?_⟩
    intro z hz
    rw [Set.Finite.mem_toFinset]
    rw [hSdef]
    exact ⟨z, hz, rfl⟩
  -- an embedding of `ℕ` into `S`, composed with the coercion to `Set ℂ`
  let e : ℕ ↪ S := Set.Infinite.natEmbedding S hSinf
  let f : ℕ → Set ℂ := fun n => (e n : Set ℂ)
  have key : ∀ n : ℕ, ∃ z ∈ P, f n = connectedComponentIn P z := by
    intro n
    have h1 : f n ∈ S := (e n).2
    rw [hSdef] at h1
    exact h1
  choose w hwP hwEq using key
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    exact e.injective (Subtype.ext hnm)
  · intro k
    rw [hwEq k]
    exact connectedComponentIn_subset P (w k)
  · intro k
    rw [hwEq k]
    exact isPreconnected_connectedComponentIn
  · intro k C hC hCP hne
    obtain ⟨u, hufk, huC⟩ := hne
    rw [hwEq k] at hufk
    have hzeq : connectedComponentIn P (w k) = connectedComponentIn P u :=
      connectedComponentIn_eq hufk
    rw [hwEq k, hzeq]
    exact hC.subset_connectedComponentIn huC hCP

end Work.HornB
