import Mathlib

namespace Work.BoxShrink.Bubble.Plane

/-- If `B` is closed and both `A` and `B` have empty interior, then `A ∪ B` has empty interior.
Only closedness of the *right* summand is needed (and no separation axioms on `X`). -/
theorem interior_union_eq_empty_of_isClosed_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed B) (hAi : interior A = ∅) (hBi : interior B = ∅) :
    interior (A ∪ B) = ∅ := by
  have h1 : interior (A ∪ B) \ B ⊆ interior A :=
    interior_maximal (fun x hx => (interior_subset hx.1).resolve_right hx.2)
      (isOpen_interior.sdiff hB)
  rw [hAi] at h1
  have h2 : interior (A ∪ B) ⊆ B := by
    intro x hx
    by_contra hxB
    exact h1 ⟨hx, hxB⟩
  have h3 : interior (A ∪ B) ⊆ interior B := interior_maximal h2 isOpen_interior
  rw [hBi] at h3
  exact Set.subset_empty_iff.mp h3

theorem interior_iUnion_fin_eq_empty {X : Type*} [TopologicalSpace X] {n : ℕ} {f : Fin n → Set X}
    (hcl : ∀ i, IsClosed (f i)) (hd : ∀ i, interior (f i) = ∅) :
    interior (⋃ i, f i) = ∅ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (⋃ i : Fin (n + 1), f i) = f 0 ∪ ⋃ i : Fin n, f i.succ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        rcases (Fin.exists_fin_succ (P := fun i => x ∈ f i)).mp ⟨i, hi⟩ with h | ⟨j, hj⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, hj⟩
      · rintro (h | ⟨j, hj⟩)
        · exact ⟨0, h⟩
        · exact ⟨Fin.succ j, hj⟩
    rw [hsplit]
    exact interior_union_eq_empty_of_isClosed_right
      (isClosed_iUnion_of_finite fun i => hcl i.succ) (hd 0)
      (ih (fun i => hcl i.succ) (fun i => hd i.succ))

end Work.BoxShrink.Bubble.Plane
