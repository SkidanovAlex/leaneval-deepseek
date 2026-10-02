import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Set

/-- A finite union of closed sets (indexed by a `Finset`) is closed. -/
lemma isClosed_finset_biUnion {α : Type*} [TopologicalSpace α] {ι : Type*} {F : ι → Set α}
    (hF : ∀ i, IsClosed (F i)) (u : Finset ι) : IsClosed (⋃ i ∈ u, F i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u _ ih => rw [Finset.set_biUnion_insert]; exact (hF a).union ih

/-- A preconnected set contained in the union of two disjoint closed sets lies in one of them. -/
lemma isPreconnected_subset_left_or_right_of_disjoint_closed {α : Type*} [TopologicalSpace α]
    {s u v : Set α} (hs : IsPreconnected s) (hu : IsClosed u) (hv : IsClosed v)
    (hdis : Disjoint u v) (hsub : s ⊆ u ∪ v) : s ⊆ u ∨ s ⊆ v :=
  (isPreconnected_iff_subset_of_disjoint_closed.1 hs) u v hu hv hsub
    (by rw [hdis.inter_eq, inter_empty])

theorem preconnected_subset_one_of_disjoint_closed {α : Type*} [TopologicalSpace α] {ι : Type*}
    {s : Set α} (hs : IsPreconnected s) (hne : s.Nonempty) (t : Finset ι) (F : ι → Set α)
    (hF : ∀ i, IsClosed (F i))
    (hdis : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (F i) (F j))
    (hsub : s ⊆ ⋃ i ∈ t, F i) : ∃ i ∈ t, s ⊆ F i := by
  classical
  revert hF hdis hsub
  induction t using Finset.induction_on generalizing F with
  | empty =>
    intro _hF _hdis hsub
    have h0 : (⋃ i ∈ (∅ : Finset ι), F i) = (∅ : Set α) := by simp
    rw [h0] at hsub
    exact absurd (subset_empty_iff.1 hsub) hne.ne_empty
  | insert a u ha ih =>
    intro hF hdis hsub
    rw [Finset.set_biUnion_insert] at hsub
    have hclosedU : IsClosed (⋃ i ∈ u, F i) := isClosed_finset_biUnion hF u
    have hdisab : Disjoint (F a) (⋃ i ∈ u, F i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hdis a (Finset.mem_insert_self a u) i (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    rcases isPreconnected_subset_left_or_right_of_disjoint_closed hs (hF a) hclosedU hdisab hsub
      with h | h
    · exact ⟨a, Finset.mem_insert_self a u, h⟩
    · obtain ⟨i, hi, hsi⟩ :=
        ih F hF (fun i hi j hj hij =>
          hdis i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij) h
      exact ⟨i, Finset.mem_insert_of_mem hi, hsi⟩

end Work.LandLeaves
