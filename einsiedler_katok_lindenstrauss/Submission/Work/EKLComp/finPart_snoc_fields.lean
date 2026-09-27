import Mathlib

namespace Work.EKLComp

/-- If `A : Fin n → Set X` is a measurable, pairwise disjoint family and `F` is a measurable set,
disjoint from all the `A m`, with `F ∪ ⋃ m, A m = univ`, then the family
`Fin.snoc A F : Fin (n+1) → Set X` (which appends `F` in the last position) consists of
measurable sets, is pairwise disjoint, and covers `X`. -/
theorem finPart_snoc_fields {X : Type*} [MeasurableSpace X] {n : ℕ} (A : Fin n → Set X) (F : Set X)
    (hA : ∀ m, MeasurableSet (A m)) (hF : MeasurableSet F)
    (hdisj : ∀ m m', m ≠ m' → Disjoint (A m) (A m')) (hdisjF : ∀ m, Disjoint (A m) F)
    (hcover : ∀ x, x ∈ F ∨ ∃ m, x ∈ A m) :
    (∀ k : Fin (n+1), MeasurableSet ((Fin.snoc A F : Fin (n+1) → Set X) k)) ∧
    (Pairwise fun k l : Fin (n+1) =>
        Disjoint ((Fin.snoc A F : Fin (n+1) → Set X) k)
                 ((Fin.snoc A F : Fin (n+1) → Set X) l)) ∧
    (⋃ k : Fin (n+1), (Fin.snoc A F : Fin (n+1) → Set X) k) = (Set.univ : Set X) := by
  have hc : ∀ i : Fin n, (Fin.snoc A F : Fin (n+1) → Set X) i.castSucc = A i :=
    fun i => Fin.snoc_castSucc (α := fun _ => Set X) F A i
  have hl : (Fin.snoc A F : Fin (n+1) → Set X) (Fin.last n) = F :=
    Fin.snoc_last (α := fun _ => Set X) F A
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · rw [hc i]; exact hA i
    · rw [hl]; exact hF
  · intro k l hkl
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last l with ⟨j, rfl⟩ | rfl
      · rw [hc i, hc j]
        exact hdisj i j (fun h => hkl (by rw [h]))
      · rw [hc i, hl]; exact hdisjF i
    · rcases Fin.eq_castSucc_or_eq_last l with ⟨j, rfl⟩ | rfl
      · rw [hl, hc j]; exact (hdisjF j).symm
      · exact absurd rfl hkl
  · apply Set.eq_univ_of_forall
    intro x
    rcases hcover x with hx | ⟨m, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Fin.last n, by rw [hl]; exact hx⟩
    · exact Set.mem_iUnion.mpr ⟨m.castSucc, by rw [hc m]; exact hx⟩

end Work.EKLComp
