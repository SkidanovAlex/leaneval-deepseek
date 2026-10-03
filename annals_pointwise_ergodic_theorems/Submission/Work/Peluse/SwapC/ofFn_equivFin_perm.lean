import Mathlib

namespace Work.Peluse.SwapC

/-- If `e : F ≃ Fin F.card` is any bijection between the elements of a finset `F` and `Fin F.card`,
then listing the elements of `F` through the inverse of `e` gives a permutation of `F.toList`.

(Any bijection works; the concrete equivalence `F.equivFin` is only used through this lemma.) -/
theorem perm_ofFn_of_equiv {α : Type*} (F : Finset α) (e : F ≃ Fin F.card) :
    (List.ofFn (fun k : Fin F.card => (e.symm k).1)).Perm F.toList := by
  have hinj : Function.Injective (fun k : Fin F.card => (e.symm k).1) := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hsurj : ∀ x : α, x ∈ F ↔ ∃ i, (e.symm i).1 = x := by
    intro x
    constructor
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact (e.symm i).2
  have hnodup : (↑(List.ofFn (fun k : Fin F.card => (e.symm k).1)) : Multiset α).Nodup :=
    Multiset.coe_nodup.mpr (List.nodup_ofFn.mpr hinj)
  have hnodup2 : (↑F.toList : Multiset α).Nodup := Multiset.coe_nodup.mpr F.nodup_toList
  have hmem : ∀ a, a ∈ (↑(List.ofFn (fun k : Fin F.card => (e.symm k).1)) : Multiset α) ↔
      a ∈ (↑F.toList : Multiset α) := by
    intro a
    rw [Multiset.mem_coe, Multiset.mem_coe, List.mem_ofFn, Finset.mem_toList]
    exact (hsurj a).symm
  exact Multiset.coe_eq_coe.mp ((Multiset.Nodup.ext hnodup hnodup2).mpr hmem)

/-- The list of the values of `h` over the elements of a finset `F`, indexed by `Fin F.card` through
the canonical equivalence `F.equivFin`, is a permutation of `h` applied to `F.toList`. -/
theorem ofFn_equivFin_perm {α β : Type*} [DecidableEq α] (F : Finset α) (h : α → β) :
    (List.ofFn (fun k : Fin F.card => h ((F.equivFin.symm k).1))).Perm (F.toList.map h) := by
  have h1 := (perm_ofFn_of_equiv F F.equivFin).map h
  have h2 : (List.ofFn (fun k : Fin F.card => (F.equivFin.symm k).1)).map h
      = List.ofFn (fun k : Fin F.card => h ((F.equivFin.symm k).1)) := List.map_ofFn
  rw [h2] at h1
  exact h1

end Work.Peluse.SwapC
