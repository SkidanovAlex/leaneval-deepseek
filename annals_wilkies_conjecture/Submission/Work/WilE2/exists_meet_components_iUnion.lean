import Mathlib

namespace Work.WilE2

open Set

/-- Combine finitely many finite "component-meeting" sets.

If each `A i` carries a finite set `s i` of size at most `N i` meeting every
connected component of `A i` (from within `A i`), then the union of the `s i`
meets every connected component of `⋃ i, A i`, and has size at most `∑ i, N i`.

The point is that connected components grow with the ambient set: if `x` and
`y` lie in the same connected component of `A i ⊆ ⋃ i, A i`, then they lie in
the same connected component of the union. -/
theorem exists_meet_components_iUnion {ι X : Type*} [TopologicalSpace X] [Fintype ι]
    (A : ι → Set X) (N : ι → ℕ)
    (h : ∀ i, ∃ s : Finset X, s.card ≤ N i ∧ (↑s : Set X) ⊆ A i ∧
      ∀ x ∈ A i, ∃ y ∈ s, connectedComponentIn (A i) x = connectedComponentIn (A i) y) :
    ∃ s : Finset X, s.card ≤ ∑ i, N i ∧ (↑s : Set X) ⊆ ⋃ i, A i ∧
      ∀ x ∈ ⋃ i, A i, ∃ y ∈ s,
        connectedComponentIn (⋃ i, A i) x = connectedComponentIn (⋃ i, A i) y := by
  classical
  choose s hs using h
  refine ⟨Finset.univ.biUnion s, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion s).card ≤ ∑ i ∈ Finset.univ, (s i).card :=
          Finset.card_biUnion_le
      _ = ∑ i, (s i).card := by simp
      _ ≤ ∑ i, N i := Finset.sum_le_sum (fun i _ => (hs i).1)
  · intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, -, hi⟩ := hx
    exact mem_iUnion.mpr ⟨i, (hs i).2.1 hi⟩
  · intro x hx
    rw [mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨y, hy, hxy⟩ := (hs i).2.2 x hi
    refine ⟨y, ?_, ?_⟩
    · rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, hy⟩
    · have hsub : A i ⊆ ⋃ i, A i := fun z hz => mem_iUnion.mpr ⟨i, hz⟩
      have hmem : y ∈ connectedComponentIn (A i) x := by
        rw [hxy]
        exact mem_connectedComponentIn ((hs i).2.1 hy)
      exact connectedComponentIn_eq (connectedComponentIn_mono x hsub hmem)

end Work.WilE2
