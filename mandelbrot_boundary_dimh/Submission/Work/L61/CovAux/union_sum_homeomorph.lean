import Mathlib

namespace Work.L61.CovAux

/-- For disjoint open sets `A B ⊆ E`, the disjoint union of the subtypes is
homeomorphic to the subtype of the union, in the evident way. -/
theorem union_sum_homeomorph {E : Type*} [TopologicalSpace E] {A B : Set E}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) :
    ∃ e : (↥A ⊕ ↥B) ≃ₜ ↥(A ∪ B),
      (∀ x : ↥A, e (Sum.inl x) = ⟨(x : E), Or.inl x.2⟩) ∧
      (∀ x : ↥B, e (Sum.inr x) = ⟨(x : E), Or.inr x.2⟩) := by
  let F : (↥A ⊕ ↥B) → ↥(A ∪ B) :=
    Sum.elim (fun x : ↥A => (⟨(x : E), Or.inl x.2⟩ : ↥(A ∪ B)))
             (fun x : ↥B => (⟨(x : E), Or.inr x.2⟩ : ↥(A ∪ B)))
  have hfc : Continuous (fun x : ↥A => (⟨(x : E), Or.inl x.2⟩ : ↥(A ∪ B))) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hgc : Continuous (fun x : ↥B => (⟨(x : E), Or.inr x.2⟩ : ↥(A ∪ B))) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hfo : IsOpenMap (fun x : ↥A => (⟨(x : E), Or.inl x.2⟩ : ↥(A ∪ B))) := by
    apply IsOpenMap.subtype_mk
    exact hA.isOpenMap_subtype_val
  have hgo : IsOpenMap (fun x : ↥B => (⟨(x : E), Or.inr x.2⟩ : ↥(A ∪ B))) := by
    apply IsOpenMap.subtype_mk
    exact hB.isOpenMap_subtype_val
  have hcont : Continuous F := by
    change Continuous (Sum.elim (fun x : ↥A => (⟨(x : E), Or.inl x.2⟩ : ↥(A ∪ B)))
             (fun x : ↥B => (⟨(x : E), Or.inr x.2⟩ : ↥(A ∪ B))))
    exact Continuous.sumElim hfc hgc
  have hopen : IsOpenMap F := by
    change IsOpenMap (Sum.elim (fun x : ↥A => (⟨(x : E), Or.inl x.2⟩ : ↥(A ∪ B)))
             (fun x : ↥B => (⟨(x : E), Or.inr x.2⟩ : ↥(A ∪ B))))
    exact IsOpenMap.sumElim hfo hgo
  have hinj : Function.Injective F := by
    intro a b hab
    rcases a with x | x <;> rcases b with y | y
    · have hxy : x = y := Subtype.ext (by
        have := congrArg Subtype.val hab
        simpa [F] using this)
      rw [hxy]
    · exfalso
      have hval : (x : E) = (y : E) := by
        have := congrArg Subtype.val hab
        simpa [F] using this
      exact Set.disjoint_left.mp hAB x.2 (hval ▸ y.2)
    · exfalso
      have hval : (x : E) = (y : E) := by
        have := congrArg Subtype.val hab
        simpa [F] using this
      exact Set.disjoint_left.mp hAB y.2 (hval.symm ▸ x.2)
    · have hxy : x = y := Subtype.ext (by
        have := congrArg Subtype.val hab
        simpa [F] using this)
      rw [hxy]
  have hsurj : Function.Surjective F := by
    intro y
    by_cases hy : (y : E) ∈ A
    · refine ⟨Sum.inl ⟨(y : E), hy⟩, ?_⟩
      exact Subtype.ext rfl
    · refine ⟨Sum.inr ⟨(y : E), ?_⟩, ?_⟩
      · rcases y.2 with h | h
        · exact absurd h hy
        · exact h
      · exact Subtype.ext rfl
  refine ⟨(Equiv.ofBijective F ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    ?_, ?_⟩
  · intro x; rfl
  · intro x; rfl

end Work.L61.CovAux
