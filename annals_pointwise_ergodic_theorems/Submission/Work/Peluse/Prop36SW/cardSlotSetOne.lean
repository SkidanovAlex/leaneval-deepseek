import Mathlib
import Submission.Work.Peluse.UControl.peluseLadder

/-!
# The slot sets at multiplicity one

Peluse's Lemma 5.7 indexes its hypothesis by the *nonempty* subsets `ω` of the slots
`Slot ι k = Σ i, Fin (k i)`, and by `FamIdx kω = Σ ω, Fin (kω ω)`.  When every multiplicity is
one, `Slot α (fun _ => 1) ≃ α`, so the nonempty slot sets are exactly the nonempty finite subsets
of `α` and both index types have cardinality `2 ^ |α| - 1`.

This file provides that dictionary: the equivalence `SlotSet α (fun _ => 1) ≃ {T : Finset α //
T.Nonempty}` and the two cardinality computations.
-/

set_option autoImplicit false

namespace Work.Peluse.Prop36SW

/-- At multiplicity one the slot `(i,0)` is just the index `i`. -/
def slotEquivOne (α : Type) : Work.Peluse.UControl.Slot α (fun _ => 1) ≃ α :=
  Equiv.sigmaUnique α (fun _ : α => Fin 1)

/-- The nonempty slot-sets at multiplicity one are the nonempty finite subsets of `α`. -/
def slotSetEquivOne (α : Type) :
    Work.Peluse.UControl.SlotSet α (fun _ => 1) ≃ {T : Finset α // T.Nonempty} :=
  Equiv.subtypeEquiv (Equiv.finsetCongr (slotEquivOne α)) (by
    intro s
    rw [Equiv.finsetCongr_apply]
    exact Finset.map_nonempty.symm)

/-- The number of nonempty finite subsets of a finite type. -/
theorem card_finset_nonempty (β : Type) [Fintype β] [DecidableEq β] :
    Fintype.card {T : Finset β // T.Nonempty} = 2 ^ Fintype.card β - 1 := by
  classical
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun T : Finset β => T.Nonempty))
      = (Finset.univ : Finset (Finset β)).erase ∅ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hT
      exact ⟨fun h0 => (Finset.not_nonempty_iff_eq_empty.mpr h0) hT, trivial⟩
    · intro hT
      exact Finset.nonempty_iff_ne_empty.mpr hT.1
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset]

/-- The cardinality of the slot sets at multiplicity one. -/
theorem card_slotSet_one (α : Type) [Fintype α] [DecidableEq α] :
    Fintype.card (Work.Peluse.UControl.SlotSet α (fun _ => 1)) = 2 ^ Fintype.card α - 1 := by
  classical
  rw [Fintype.card_congr (slotSetEquivOne α)]
  exact card_finset_nonempty α

/-- The cardinality of the family index type at multiplicity one. -/
theorem card_famIdx_one (α : Type) [Fintype α] [DecidableEq α] :
    Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : α => 1)
        (fun _ : Work.Peluse.UControl.SlotSet α (fun _ => 1) => 1))
      = 2 ^ Fintype.card α - 1 := by
  classical
  rw [Fintype.card_congr (Equiv.sigmaUnique (Work.Peluse.UControl.SlotSet α (fun _ => 1))
        (fun _ : Work.Peluse.UControl.SlotSet α (fun _ => 1) => Fin 1))]
  exact card_slotSet_one α

theorem cardSlotSetOne (α : Type) [Fintype α] [DecidableEq α] :
    (Nonempty (Work.Peluse.UControl.SlotSet α (fun _ => 1) ≃ {T : Finset α // T.Nonempty}))
      ∧ Fintype.card (Work.Peluse.UControl.SlotSet α (fun _ => 1)) = 2 ^ Fintype.card α - 1
      ∧ Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : α => 1)
          (fun _ : Work.Peluse.UControl.SlotSet α (fun _ => 1) => 1)) = 2 ^ Fintype.card α - 1 :=
  ⟨⟨slotSetEquivOne α⟩, card_slotSet_one α, card_famIdx_one α⟩

end Work.Peluse.Prop36SW
