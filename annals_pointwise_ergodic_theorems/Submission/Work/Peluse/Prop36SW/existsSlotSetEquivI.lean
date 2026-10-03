import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily
import Submission.Work.Peluse.UControl.peluseLadder

/-!
# The level-`j` slot sets at multiplicity one are the level-`j` index sets `I_j`

Peluse's index construction (`Work.Peluse.UControl.IdxDatum`) has, at every level `j`, a type of
*slots* `D.S j`; the level-`j` indices `I_j = D.I j` are the nonempty finite subsets of `D.S j`.

In the ladder of `Work.Peluse.Prop36SW` the levels are instantiated at multiplicity one, so the
level-`(j+1)` slots are `Slot (D.S (j+1)) (fun _ => 1) = Σ i : D.S (j+1), Fin 1`, and the index
type used by the ladder is `SlotSet (D.S j) (fun _ => 1) = {s : Finset (Σ i, Fin 1) // s.Nonempty}`.
Since `Fin 1` is a singleton, the first projection is a bijection onto `D.S j`, and hence the
nonempty finite subsets correspond exactly to `I_j`.

This file records that dictionary: `slotSetEquivI` (for a general index type `α`) and the statement
`existsSlotSetEquivI` that the equivalence can be chosen so that its forward map is *literally* the
first projection on the underlying finsets (this is the form consumed by `sumSlotDir`, which needs
to rewrite a sum over the slots of `ω` as a sum over `ω.1.image (fun s => s.1)` via
`Finset.sum_image`).
-/

set_option autoImplicit false

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

/-- At multiplicity one the slot `(i, 0)` is just the index `i`: the canonical equivalence of a
`Σ`-type over a singleton (`Fin 1`) fibre with its index type. -/
def slotEquivOneI (α : Type) : Slot α (fun _ => 1) ≃ α :=
  Equiv.sigmaUnique α (fun _ : α => Fin 1)

/-- At multiplicity one the nonempty slot-sets are exactly the nonempty finite subsets of the index
type (transported along the first projection `Σ i, Fin 1 → α`). -/
def slotSetEquivI (α : Type) [DecidableEq α] :
    SlotSet α (fun _ => 1) ≃ {T : Finset α // T.Nonempty} :=
  Equiv.subtypeEquiv (Equiv.finsetCongr (slotEquivOneI α)) (by
    intro s
    rw [Equiv.finsetCongr_apply]
    exact Finset.map_nonempty.symm)

/-- The forward map of `slotSetEquivI` is the first projection on the underlying finsets. -/
lemma slotSetEquivI_apply (α : Type) [DecidableEq α] (s : SlotSet α (fun _ => 1)) :
    ((slotSetEquivI α) s).1 = s.1.image (fun t => t.1) := by
  show (Equiv.finsetCongr (slotEquivOneI α)) s.1 = s.1.image (fun t => t.1)
  rw [Equiv.finsetCongr_apply, Finset.map_eq_image]
  congr 1

/-- **The level-`j` slot sets at multiplicity one are the index sets `I_j`**, via an equivalence
whose forward map is the first projection on the underlying finsets. -/
theorem existsSlotSetEquivI (D : Work.Peluse.UControl.IdxDatum) (j : ℕ) :
    ∃ e : Work.Peluse.UControl.SlotSet (D.S j) (fun _ => 1) ≃ D.I j,
      ∀ omega, (e omega).1 = omega.1.image (fun s => s.1) := by
  classical
  exact ⟨slotSetEquivI (D.S j), fun omega => slotSetEquivI_apply (D.S j) omega⟩

end Work.Peluse.Prop36SW
