import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.FibreResidual
import Submission.Work.PerSector.SlotAdditive
import Submission.Work.PerSector.aemeasurable_slotFibreMass
import Submission.Work.PerSector.sum_tBamp_normSq_slotPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.ThetaDefs` — the slot reassembly equivalence

The single configuration-space equivalence

`slotTheta S e : X |S| × (SlotOut N S → ℝ³) ≃ᵐ X N`,  `(x, y) ↦ slotComb S (x ∘ e) y`

that turns the `N`-particle slot piece of `Work.PerSector.slotPiece` into the
`|S|`-particle fibre of `Work.PerSector.slotFibreState`: reassembling the in-box configuration
`x` (transported along the bijection `e : SlotIn N S ≃ Fin |S|`) with the outside configuration
`y` gives exactly the `N`-particle configuration on which the slot-piece density is read.

It is the composition
`(slotME S).symm ∘ ((reindex along e) × id)` of the two standard measure-preserving
equivalences, hence measure preserving (`slotTheta_measurePreserving`); the corpus box pulls back
to the product of the `|S|`-particle box and the out-of-box slot box
(`slotTheta_preimage_abox`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.PerSector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- **The slot reassembly equivalence**: send `(x, y)` to the `N`-particle configuration whose
in-box slots are the coordinates of `x` (read along the bijection `e`) and whose outside slots are
the coordinates of `y`. -/
noncomputable def slotTheta (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) :
    (X S.card × (SlotOut N S → ℝ³)) ≃ᵐ X N :=
  ((MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm).prodCongr
      (MeasurableEquiv.refl (SlotOut N S → ℝ³))).trans
    (Work.PerSector.Work.PerSector.slotME S).symm

/-- The defining equation of `slotTheta`. -/
theorem slotTheta_apply (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (p : X S.card × (SlotOut N S → ℝ³)) :
    slotTheta S e p = slotComb S (fun i : SlotIn N S => p.1 (e i)) p.2 := by
  obtain ⟨x, y⟩ := p
  rw [slotTheta, MeasurableEquiv.trans_apply]
  change (Work.PerSector.Work.PerSector.slotME S).symm
      ((MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm) x, y)
    = slotComb S (fun i : SlotIn N S => x (e i)) y
  rw [Work.PerSector.Work.PerSector.slotME_symm_apply]
  congr 1
  funext k
  show (MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm) x k = x (e k)
  conv_lhs => rw [← e.symm_apply_apply k]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]

/-- `slotTheta` is measure preserving. -/
theorem slotTheta_measurePreserving (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) :
    MeasurePreserving (slotTheta S e) (volume : Measure (X S.card × (SlotOut N S → ℝ³)))
      (volume : Measure (X N)) := by
  have hinst : (Finset.Subtype.fintype S : Fintype (SlotIn N S)) =
      Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  have hslot : MeasurePreserving (Work.PerSector.Work.PerSector.slotME S)
      (volume : Measure (X N))
      (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³))) := by
    rw [Work.PerSector.Work.PerSector.slotME, hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
  have hprod : MeasurePreserving (fun p : X S.card × (SlotOut N S → ℝ³) =>
      (((MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm) p.1), p.2))
      (volume : Measure (X S.card × (SlotOut N S → ℝ³)))
      (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³))) := by
    have h := (volume_measurePreserving_piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm).prod
      (MeasurePreserving.id (volume : Measure (SlotOut N S → ℝ³)))
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact h
  have hcomp := hslot.symm.comp hprod
  convert hcomp using 1
  funext p
  rw [slotTheta, MeasurableEquiv.trans_apply]
  rfl

/-- **The corpus box pulls back to the product of the `|S|`-particle box and the out-of-box slot
box**: a reassembled configuration lies in `abox N L` exactly when the in-box coordinates lie in
the `|S|`-particle box and the outside coordinates lie in the slot box over the corpus cube. -/
theorem slotTheta_preimage_abox (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (L : ℝ) :
    (slotTheta S e) ⁻¹' (abox N L) = abox S.card L ×ˢ slotBox (ι := SlotOut N S) (acube L) := by
  ext p
  simp only [Set.mem_preimage, mem_abox_iff, Set.mem_prod, mem_slotBox_iff]
  constructor
  · intro hp
    refine ⟨fun k => ?_, fun j => ?_⟩
    · have h1 := hp (e.symm k)
      rw [slotTheta_apply, slotComb_apply, dif_pos (e.symm k).2] at h1
      rwa [e.apply_symm_apply] at h1
    · have h1 := hp j.1
      rw [slotTheta_apply, slotComb_apply, dif_neg j.2] at h1
      exact h1
  · rintro ⟨hx, hy⟩ i
    rw [slotTheta_apply, slotComb_apply]
    by_cases h : i ∈ S
    · rw [dif_pos h]; exact hx (e ⟨i, h⟩)
    · rw [dif_neg h]; exact hy ⟨i, h⟩

/-- Membership of a reassembled configuration in the slot set: exactly the in-box coordinates of
`x` lie in `B` (on the support, `y` already lies outside `B`). -/
theorem slotTheta_mem_slotSet_iff (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    {B : Set ℝ³} (p : X S.card × (SlotOut N S → ℝ³)) :
    slotTheta S e p ∈ slotSet B S
      ↔ (∀ k : Fin S.card, p.1 k ∈ B) ∧ (∀ j : SlotOut N S, p.2 j ∉ B) := by
  rw [slotTheta_apply, slotComb_mem_slotSet_iff]
  constructor
  · rintro ⟨hz, hy⟩
    refine ⟨fun k => ?_, hy⟩
    have := hz (e.symm k)
    rwa [e.apply_symm_apply] at this
  · rintro ⟨hx, hy⟩
    exact ⟨fun i => hx (e i), hy⟩

end Work.SlotWord
