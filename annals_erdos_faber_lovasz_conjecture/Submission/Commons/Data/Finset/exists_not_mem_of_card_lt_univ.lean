import Mathlib.Data.Fintype.Card

namespace Commons.Data.Finset

theorem exists_not_mem_of_card_lt_univ {α : Type*} [Fintype α] (s : Finset α)
    (h : s.card < Fintype.card α) : ∃ x : α, x ∉ s := by
  by_contra hne
  push_neg at hne
  have hs_univ : s = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    exact hne
  have hcard : s.card = Fintype.card α := by
    rw [hs_univ, Finset.card_univ]
  exact not_lt_of_ge (le_of_eq hcard.symm) h

end Commons.Data.Finset