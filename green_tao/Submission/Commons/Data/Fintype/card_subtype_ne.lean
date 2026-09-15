import Mathlib.Data.Fintype.Card

namespace Commons.Data.Fintype

theorem card_subtype_ne {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card {x : α // x ≠ a} = Fintype.card α - 1 := by
  classical
  let s : Finset α := Finset.univ.filter (fun x : α => x ≠ a)
  have hmem : ∀ x : α, x ∈ s ↔ x ≠ a := by
    intro x
    simp [s]
  have hs : s = Finset.univ.erase a := by
    ext x
    simp [s]
  calc
    Fintype.card {x : α // x ≠ a} = s.card := by
      exact Fintype.card_of_subtype s hmem
    _ = (Finset.univ.erase a).card := by rw [hs]
    _ = Finset.univ.card - 1 := by
      exact Finset.card_erase_of_mem (Finset.mem_univ a)
    _ = Fintype.card α - 1 := by rw [Finset.card_univ]

end Commons.Data.Fintype