import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.slotMassENN_eq_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `lintegral_sectorRegion_eq`: the lintegral form of the slot splitting

For a slot set `S : Finset (Fin N)`, a box `B ⊆ ℝ³` and a set `A ⊆ ℝ³`, put

* `t = slotSet B S ∩ {x | ∀ j : SlotOut N S, x j.1 ∈ A}` — the region of configurations in which
  exactly the slots of `S` lie in `B` and every slot *outside* `S` lies in `A`;
* `s' = slotBox (ι := SlotIn N S) B ×ˢ slotBox (ι := SlotOut N S) (A ∩ Bᶜ)` — the product of the
  in-box slot box and the out-of-box slot box.

The measurable equivalence `slotME S : X N ≃ᵐ (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)` (the
`MeasurableEquiv` version of `slotEquiv`, whose inverse is `slotComb`, and which preserves Lebesgue
measure by `volume_preserving_piEquivPiSubtypeProd`, up to the `Subsingleton` identification of the
two `Fintype` instances on the slot types) maps `t` exactly onto `s'`: the slot-set condition
`x i ∈ B ↔ i ∈ S` says that the in-slot coordinates lie in `B` and the out-slot coordinates lie
outside it, and the remaining condition says that the out-slot coordinates lie in `A`.

Changing variables along `slotME S` therefore turns the lintegral of `f` over `t` into the lintegral
of `f ∘ slotComb` over `s'`, which is the stated identity.  This is the `lintegral`-level companion
of the fibre decomposition `slotMassENN_eq_fibre`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

/-- **The sector region is the slot box under the slot splitting.**  The preimage of the region
`slotSet B S ∩ {x | ∀ j : SlotOut N S, x j.1 ∈ A}` under the slot-splitting equivalence `slotME S`
is the product of the in-box slot box `B^{SlotIn}` and the out-of-box slot box
`(A ∩ Bᶜ)^{SlotOut}`. -/
theorem slotME_symm_preimage_sectorRegion {N : ℕ} (S : Finset (Fin N))
    (A B : Set (EuclideanSpace ℝ (Fin 3))) :
    (Work.PerSector.Work.PerSector.slotME S).symm ⁻¹'
        (Work.PerSector.slotSet B S ∩ {x : Submission.BoseGases.X N |
          ∀ j : Work.PerSector.SlotOut N S, x j.1 ∈ A})
      = Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B ×ˢ
        Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ) := by
  ext p
  obtain ⟨z, y⟩ := p
  -- the reassembled configuration has `y j` in its out-of-`S` slots
  have hout : ∀ j : Work.PerSector.SlotOut N S,
      Work.PerSector.slotComb S z y j.1 = y j := fun j => by
    rw [Work.PerSector.slotComb_apply, dif_neg j.2]
  simp only [Set.mem_preimage, Work.PerSector.Work.PerSector.slotME_symm_apply,
    Set.mem_prod, Work.PerSector.mem_slotBox_iff, Set.mem_inter_iff, Set.mem_compl_iff,
    Work.PerSector.slotComb_mem_slotSet_iff, Set.mem_ofPred_eq]
  constructor
  · -- the sector region is contained in the slot box
    rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun j => ⟨by simpa only [← hout j] using h3 j, h2 j⟩⟩
  · -- and conversely
    rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun j => (h2 j).2⟩, fun j => by simpa only [hout j] using (h2 j).1⟩

theorem lintegral_sectorRegion_eq {N : ℕ} (S : Finset (Fin N))
    (A B : Set (EuclideanSpace ℝ (Fin 3))) (f : Submission.BoseGases.X N → ENNReal) :
    ∫⁻ x in (Work.PerSector.slotSet B S ∩ {x : Submission.BoseGases.X N |
        ∀ j : Work.PerSector.SlotOut N S, x j.1 ∈ A}), f x
      = ∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B
          ×ˢ Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ),
        f (Work.PerSector.slotComb S p.1 p.2) := by
  classical
  -- `volume_preserving_piEquivPiSubtypeProd` uses the generic `Fintype` instance
  -- `Subtype.fintype` for the slot types, while the statement uses `Finset.Subtype.fintype S`;
  -- `Fintype` is a `Subsingleton`, so the two instances are equal and the lemma applies.
  have hinst : (Finset.Subtype.fintype S : Fintype (Work.PerSector.SlotIn N S))
      = Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving (⇑(Work.PerSector.Work.PerSector.slotME S))
      (volume : Measure (Submission.BoseGases.X N))
      (volume : Measure ((Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3)) ×
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => EuclideanSpace ℝ (Fin 3))
      (fun i : Fin N => i ∈ S)
  -- the sector region is the preimage of the slot box along the slot splitting
  have hpre := slotME_symm_preimage_sectorRegion (N := N) S A B
  -- change variables along the (measure preserving) inverse slot splitting
  have hcv := (MeasurePreserving.symm (Work.PerSector.Work.PerSector.slotME S) hmp).setLIntegral_comp_preimage_emb
      (Work.PerSector.Work.PerSector.slotME S).symm.measurableEmbedding f
      (Work.PerSector.slotSet B S ∩ {x : Submission.BoseGases.X N |
        ∀ j : Work.PerSector.SlotOut N S, x j.1 ∈ A})
  rw [hpre] at hcv
  -- the transported integrand is the integrand of the statement
  have hcong : (∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B ×ˢ
        Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ),
        f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      = ∫⁻ p in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B ×ˢ
        Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S) (A ∩ Bᶜ),
        f (Work.PerSector.slotComb S p.1 p.2) := by
    refine lintegral_congr fun p => ?_
    obtain ⟨z, y⟩ := p
    rw [Work.PerSector.Work.PerSector.slotME_symm_apply]
  exact hcv.symm.trans hcong

end Work.BoseKinLoc.Sector
