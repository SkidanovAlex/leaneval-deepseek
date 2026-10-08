import Mathlib

namespace Work.CORE4.A7FGB

/-- The support of a permutation is invariant under the permutation itself:
`x` is moved iff `f x` is moved. -/
lemma mem_support_map_iff {α : Type*} [DecidableEq α] [Fintype α] (f : Equiv.Perm α) (x : α) :
    x ∈ f.support ↔ f x ∈ f.support := by
  rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support]
  constructor
  · intro h hc; exact h (f.injective hc)
  · intro h hc; exact h (congrArg f hc)

/-- An involution on a 4-element support is determined by its value at a single
point of that support.  Indeed the support splits into the two 2-cycles
`{a, w a}` and its (two-element) complement inside the support, and an
involution that moves every point of that complement must exchange its two
elements. -/
theorem involution_support_injective (T : Finset (Fin 7)) (hT : T.card = 4) (a : Fin 7) (ha : a ∈ T)
    (w w' : Equiv.Perm (Fin 7)) (hw : w * w = 1) (hw' : w' * w' = 1)
    (hws : w.support = T) (hw's : w'.support = T) (h : w a = w' a) : w = w' := by
  have hww : ∀ x, w (w x) = x := fun x => by rw [← Equiv.Perm.mul_apply, hw]; rfl
  have hw'w' : ∀ x, w' (w' x) = x := fun x => by rw [← Equiv.Perm.mul_apply, hw']; rfl
  have hTmem : ∀ x, x ∈ T → w x ≠ x := by
    intro x hx
    rw [← Equiv.Perm.mem_support, hws]
    exact hx
  have hTmem' : ∀ x, x ∈ T → w' x ≠ x := by
    intro x hx
    rw [← Equiv.Perm.mem_support, hw's]
    exact hx
  have hmapT : ∀ x, x ∈ T → w x ∈ T := by
    intro x hx
    have hx' : x ∈ w.support := by rw [hws]; exact hx
    rw [← hws]
    exact (mem_support_map_iff w x).mp hx'
  have hmapT' : ∀ x, x ∈ T → w' x ∈ T := by
    intro x hx
    have hx' : x ∈ w'.support := by rw [hw's]; exact hx
    rw [← hw's]
    exact (mem_support_map_iff w' x).mp hx'
  have haw : w a ≠ a := by
    rw [← Equiv.Perm.mem_support, hws]
    exact ha
  apply Equiv.ext
  intro x
  by_cases hxT : x ∈ T
  · have hwx_ne : w x ≠ x := hTmem x hxT
    have hw'x_ne : w' x ≠ x := hTmem' x hxT
    by_cases hxa : x = a
    · rw [hxa]; exact h
    by_cases hxwa : x = w a
    · rw [hxwa, hww a, h, hw'w']
    · have h1 : w x ≠ a := by
        intro hc
        exact hxwa (by rw [← hww x, hc])
      have h2 : w x ≠ w a := by
        intro hc
        exact hxa (w.injective hc)
      have h3 : w' x ≠ a := by
        intro hc
        exact hxwa (by rw [← hw'w' x, hc, ← h])
      have h4 : w' x ≠ w a := by
        intro hc
        exact hxa (w'.injective (by rw [hc]; exact h))
      set S : Finset (Fin 7) := (T.erase a).erase (w a) with hSdef
      have hxS : x ∈ S := by
        rw [hSdef, Finset.mem_erase, Finset.mem_erase]
        exact ⟨hxwa, hxa, hxT⟩
      have hwxS : w x ∈ S := by
        rw [hSdef, Finset.mem_erase, Finset.mem_erase]
        exact ⟨h2, h1, hmapT x hxT⟩
      have hw'xS : w' x ∈ S := by
        rw [hSdef, Finset.mem_erase, Finset.mem_erase]
        exact ⟨h4, h3, hmapT' x hxT⟩
      have hcardS : S.card = 2 := by
        have hwa : w a ∈ T := hmapT a ha
        rw [hSdef, Finset.card_erase_of_mem (by rw [Finset.mem_erase]; exact ⟨haw, hwa⟩),
          Finset.card_erase_of_mem ha]
        omega
      have hsub : ({x, w x} : Finset (Fin 7)) ⊆ S := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hxS
        · exact hwxS
      have hcard2 : ({x, w x} : Finset (Fin 7)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simpa using hwx_ne.symm
      have heq : ({x, w x} : Finset (Fin 7)) = S :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcardS, hcard2])
      have hmem : w' x ∈ ({x, w x} : Finset (Fin 7)) := by rw [heq]; exact hw'xS
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hh | hh
      · exact (hw'x_ne hh).elim
      · exact hh.symm
  · have hfix : w x = x := by
      by_contra hc
      exact hxT (by rw [← hws, Equiv.Perm.mem_support]; exact hc)
    have hfix' : w' x = x := by
      by_contra hc
      exact hxT (by rw [← hw's, Equiv.Perm.mem_support]; exact hc)
    rw [hfix, hfix']

end Work.CORE4.A7FGB
