import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
import Submission.Work.PerSector.slotMassENN_eq_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

open MeasureTheory
open Submission.BoseGases

/-- **Joint integrability of the slot-split integrand.**  If `f` is integrable on the
configuration box `abox N L` then `(z, y) ↦ f (slotComb S z y)` is integrable for the product of
the restricted measures on the in-box configurations `slotBox (acube L)` (over `SlotIn N S`) and the
outside configurations `slotBox (acube L)` (over `SlotOut N S`).  Indeed
`slotME S : X N ≃ᵐ (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³)` is a measure-preserving measurable
equivalence with inverse `slotComb S` and it maps `abox N L` onto the product
`slotBox (acube L) × slotBox (acube L)` (`Work.PerSector.slotME_image_abox`), so integrability
transports along `slotME` (`MeasurePreserving.integrableOn_image`), and `Measure.prod_restrict`
identifies the restricted product measure with the product of the restrictions.  Its consumers are
the a.e.-in-`y` slice integrability (`MeasureTheory.Integrable.prod_left_ae`) and the integrability
of `y ↦ ∫ z, f (slotComb S z y)` (`MeasureTheory.Integrable.integral_prod_right`).  Namespace
`Work.BoseKinLoc.Sector`; imports: Mathlib, `Submission.Work.BoseKinLoc.Defs`,
`Submission.Work.PerSector.Defs`, `Submission.Work.PerSector.slotMassENN_eq_fibre`. -/
theorem integrable_slotComb_prod {N : ℕ} (L : ℝ) (S : Finset (Fin N))
    {f : Submission.BoseGases.X N → ℝ}
    (hint : MeasureTheory.IntegrableOn f (Submission.BoseGases.abox N L)) :
    MeasureTheory.Integrable
      (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
        f (Work.PerSector.slotComb S p.1 p.2))
      (((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotIn N S → ℝ³)).restrict
          (Work.PerSector.slotBox (Submission.BoseGases.acube L)
            : Set (Work.PerSector.SlotIn N S → ℝ³))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → ℝ³)).restrict
          (Work.PerSector.slotBox (Submission.BoseGases.acube L)
            : Set (Work.PerSector.SlotOut N S → ℝ³)))) := by
  classical
  -- The two `Fintype` instances on the in-box slot type agree (`Fintype` is a `Subsingleton`):
  -- `volume_preserving_piEquivPiSubtypeProd` is stated for the generic `Subtype.fintype`.
  have hinst : (Finset.Subtype.fintype S : Fintype (Work.PerSector.SlotIn N S))
      = Subtype.fintype (fun i : Fin N => i ∈ S) := Subsingleton.elim _ _
  -- The slot splitting is measure preserving.
  have hmp : MeasurePreserving (⇑(Work.PerSector.Work.PerSector.slotME S))
      (volume : Measure (X N))
      (volume : Measure ((Work.PerSector.SlotIn N S → ℝ³) ×
        (Work.PerSector.SlotOut N S → ℝ³))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ³) (fun i : Fin N => i ∈ S)
  -- Integrability transports along `slotME` from the configuration box to the product of the
  -- two slot boxes.
  have key : IntegrableOn
      (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
        f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) (Submission.BoseGases.acube L)
        ×ˢ Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (Submission.BoseGases.acube L))
      ((volume : Measure (Work.PerSector.SlotIn N S → ℝ³)).prod
        (volume : Measure (Work.PerSector.SlotOut N S → ℝ³))) := by
    rw [← Work.PerSector.Work.PerSector.slotME_image_abox (N := N) S L]
    refine (hmp.integrableOn_image
      (Work.PerSector.Work.PerSector.slotME S).measurableEmbedding).mpr ?_
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hint
  -- The product of the restricted measures is the restriction of the product measure.
  rw [Measure.prod_restrict]
  -- `(slotME S).symm` is `slotComb S`, so the transported integrand is the stated one.
  have hfun : (fun p : (Work.PerSector.SlotIn N S → ℝ³) × (Work.PerSector.SlotOut N S → ℝ³) =>
        f ((Work.PerSector.Work.PerSector.slotME S).symm p))
      = fun p => f (Work.PerSector.slotComb S p.1 p.2) := by
    funext p
    obtain ⟨z, y⟩ := p
    exact congrArg f (Work.PerSector.Work.PerSector.slotME_symm_apply S z y)
  rw [← hfun]
  exact key

end Work.BoseKinLoc.Sector
