import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.slotSplit_integral_slotBox` — the slot splitting of a Bochner integral

The `∫`-level (Bochner) companion of `Work.SlotWord.slotSplit_lintegral_slotBox`, used by the
fibre factorisation `Work.SlotWord.WordFibreFactorisation` (PerSector README §6(R1)(a)).

**Statement.**  For a box `B ⊆ acube L`, a slot set `S`, an integrable real-valued `f : X N → ℝ`
(and one a.e.-strong measurability hypothesis, kept because it is part of the caller's interface),
*vanishing unless the outside coordinates of `S` lie outside `B` and the inside coordinates lie
inside `B`*, the `abox N L`-integral of `f` equals the iterated integral over the outside
configurations `y ∈ slotOutside L B S` and the in-box configurations `z ∈ B^{S}` of
`f (slotComb S z y)`.

**Proof.**  Three steps, mirroring the `∫⁻` proof but with change of variables for the Bochner
integral (`MeasureTheory.MeasurePreserving.setIntegral_image_emb`) instead of the `∫⁻` one:

1. the change of variables along the measurable equivalence `slotME S : X N ≃ᵐ (SlotIn N S → ℝ³) ×
   (SlotOut N S → ℝ³)` (measure preserving by
   `volume_preserving_piEquivPiSubtypeProd`), whose (inverse) image of the product of the two
   `acube L`-boxes is `abox N L`;
2. the restriction to the sub-box product `slotBox B × slotOutside L B S`.  As in the `∫⁻` version
   this needs no measurability of `B`: the auxiliary Fubini lemma
   `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` says that an integral over `t` equals the
   integral over `s ⊆ t` as soon as the integrand vanishes on `t \ s`, and here the support
   hypotheses `hout`, `hin` give exactly this vanishing (a point of the big product either has an
   in-slot coordinate outside `B`, or an outside-slot coordinate inside `B`);
3. Fubini–Tonelli on the product (`Measure.prod_restrict` + `integral_prod_symm`), in the
   `y`-outer/`z`-inner order, the integrability being transported from `hint` along the measure
   preserving equivalence (`MeasureTheory.MeasurePreserving.integrableOn_image`).
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

theorem slotSplit_integral_slotBox {N : ℕ} (L : ℝ) {B : Set (EuclideanSpace ℝ (Fin 3))}
    (S : Finset (Fin N)) (hBL : B ⊆ Submission.BoseGases.acube L)
    {f : Submission.BoseGases.X N → ℝ}
    (hmes : MeasureTheory.AEStronglyMeasurable f
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N L)))
    (hint : MeasureTheory.IntegrableOn f (Submission.BoseGases.abox N L))
    (hout : ∀ x : Submission.BoseGases.X N, f x ≠ 0 → ∀ j : Work.PerSector.SlotOut N S, x j ∉ B)
    (hin : ∀ x : Submission.BoseGases.X N, f x ≠ 0 → ∀ i : Work.PerSector.SlotIn N S, x i ∈ B) :
    ∫ x in Submission.BoseGases.abox N L, f x
      = ∫ y in Work.PerSector.slotOutside L B S,
          ∫ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B,
            f (Work.PerSector.slotComb S z y) := by
  classical
  -- the `Fintype` instance of the slot types used by `volume_preserving_piEquivPiSubtypeProd`
  have hinst : (Finset.Subtype.fintype S : Fintype (SlotIn N S)) =
      Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving (⇑(Work.PerSector.Work.PerSector.slotME S)) (volume : Measure (X N))
      (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
  -- `slotME S` maps `abox N L` onto the product of the two `acube L`-boxes
  have himg : (Work.PerSector.Work.PerSector.slotME S) '' (abox N L)
      = slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L) :=
    Work.PerSector.Work.PerSector.slotME_image_abox S L
  -- hence the inverse image of that product is `abox N L`
  have hsymm : (Work.PerSector.Work.PerSector.slotME S).symm ''
      (slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L)) = abox N L := by
    rw [← himg]
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, ⟨q, hq, hqe⟩, hpx⟩
      rw [← hpx, ← hqe]
      simpa using hq
    · intro hx
      exact ⟨_, ⟨x, hx, rfl⟩, by simp⟩
  -- Step 1: change of variables along the slot splitting
  have step1 : (∫ x in abox N L, f x)
      = ∫ p in slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L),
          f ((Work.PerSector.Work.PerSector.slotME S).symm p) := by
    have h := hmp.symm.setIntegral_image_emb
      (Work.PerSector.Work.PerSector.slotME S).symm.measurableEmbedding f
      (slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L))
    rwa [hsymm] at h
  -- the big product box is measurable
  have hPmeas : MeasurableSet (slotBox (ι := SlotIn N S) (acube L)
      ×ˢ slotBox (ι := SlotOut N S) (acube L)) :=
    (Work.PerSector.Work.PerSector.slotBox_measurable (ι := SlotIn N S)
        (Submission.BoseGases.acube_measurable L)).prod
      (Work.PerSector.Work.PerSector.slotBox_measurable (ι := SlotOut N S)
        (Submission.BoseGases.acube_measurable L))
  -- the sub-box product sits inside it
  have hPQ : slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S
      ⊆ slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L) :=
    Set.prod_mono (Work.PerSector.Work.PerSector.slotBox_mono hBL)
      (Work.PerSector.Work.PerSector.slotBox_mono Set.inter_subset_left)
  -- and the integrand vanishes off it, by `hin`/`hout`
  have hzero : ∀ p ∈ (slotBox (ι := SlotIn N S) (acube L)
        ×ˢ slotBox (ι := SlotOut N S) (acube L))
      \ (slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S),
      f ((Work.PerSector.Work.PerSector.slotME S).symm p) = 0 := by
    rintro ⟨z, y⟩ ⟨hpt, hpQ⟩
    rw [Set.mem_prod, mem_slotBox_iff, mem_slotBox_iff] at hpt
    rw [Work.PerSector.Work.PerSector.slotME_symm_apply]
    by_contra hne
    apply hpQ
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [mem_slotBox_iff]
      intro i
      have hmem := hin (slotComb S z y) hne i
      rwa [slotComb_apply, dif_pos i.2] at hmem
    · rw [mem_slotOutside_iff]
      exact ⟨hpt.2, fun j => by
        have hmem := hout (slotComb S z y) hne j
        rwa [slotComb_apply, dif_neg j.2] at hmem⟩
  -- Step 2: reduce the integration domain to the sub-box product
  have step2 : (∫ p in slotBox (ι := SlotIn N S) (acube L)
          ×ˢ slotBox (ι := SlotOut N S) (acube L),
          f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      = ∫ p in slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S,
          f ((Work.PerSector.Work.PerSector.slotME S).symm p) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hPmeas hPQ hzero
  -- integrability, transported along the measure preserving equivalence from `hint`
  have hIntP : IntegrableOn (fun p => f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      (slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L)) := by
    have h := hmp.symm.integrableOn_image
      (Work.PerSector.Work.PerSector.slotME S).symm.measurableEmbedding
      (f := f)
      (s := slotBox (ι := SlotIn N S) (acube L) ×ˢ slotBox (ι := SlotOut N S) (acube L))
    rw [hsymm] at h
    exact h.mp hint
  have hIntQ : IntegrableOn (fun p => f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      (slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S) := hIntP.mono_set hPQ
  -- Step 3: Fubini in the `y`-outer / `z`-inner order
  have step3 : (∫ p in slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S,
          f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      = ∫ y in slotOutside L B S,
          ∫ z in slotBox (ι := SlotIn N S) B, f (slotComb S z y) := by
    have hm : (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³))).restrict
          (slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S)
        = ((volume : Measure (SlotIn N S → ℝ³)).restrict (slotBox (ι := SlotIn N S) B)).prod
          ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L B S)) := by
      rw [show (volume : Measure ((SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)))
          = (volume : Measure (SlotIn N S → ℝ³)).prod (volume : Measure (SlotOut N S → ℝ³))
          from rfl]
      exact (Measure.prod_restrict _ _).symm
    have hIntQ' : Integrable (fun q => f ((Work.PerSector.Work.PerSector.slotME S).symm q))
        (((volume : Measure (SlotIn N S → ℝ³)).restrict (slotBox (ι := SlotIn N S) B)).prod
          ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L B S))) := by
      rw [← hm]
      exact hIntQ
    rw [show (∫ p in slotBox (ι := SlotIn N S) B ×ˢ slotOutside L B S,
            f ((Work.PerSector.Work.PerSector.slotME S).symm p))
        = ∫ p, f ((Work.PerSector.Work.PerSector.slotME S).symm p) ∂
            (((volume : Measure (SlotIn N S → ℝ³)).restrict (slotBox (ι := SlotIn N S) B)).prod
              ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L B S))) from by
      rw [hm]]
    rw [integral_prod_symm _ hIntQ']
    simp only [Work.PerSector.Work.PerSector.slotME_symm_apply]
  rw [step1, step2, step3]

end Work.SlotWord
