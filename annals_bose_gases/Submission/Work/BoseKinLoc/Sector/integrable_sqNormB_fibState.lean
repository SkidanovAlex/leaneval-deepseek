import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.lintegral_slotBox_slotIso
import Submission.Work.BoseKinLoc.Sector.measurable_lintegral_slotFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Sector

set_option maxHeartbeats 1000000

/-- **The box mass of the fibre is the real fibre mass.**  At every outside configuration `y`, the
box `L²`-mass `sqNormB |S| ℓ (fibState S Ψ y)` of the fibre — a Bochner integral of the squared
fibre state over `abox |S| ℓ` — is the `toReal` of the `ENNReal`-valued fibre mass
`Work.PerSector.slotFibreMass (acube ℓ) S Ψ y`, i.e. the `slotFibreMassReal` of `Submission.Work.PerSector`.
The two expressions differ only by the re-indexing `slotIso S : SlotIn N S ≃ Fin |S|` of the slot
box (`lintegral_slotBox_slotIso`) and by the passage from the Bochner to the `ENNReal` integral of
a nonnegative integrand (`integral_eq_lintegral_of_nonneg_ae`). -/
theorem sqNormB_fibState_eq_slotFibreMassReal {N : ℕ} (S : Finset (Fin N)) {ℓ : ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (y : Work.PerSector.SlotOut N S → ℝ³) :
    Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)
      = Work.PerSector.slotFibreMassReal (Submission.BoseGases.acube ℓ) S Ψ y := by
  -- (i) the Bochner box mass of the fibre is the `toReal` of the `ENNReal` box mass
  have hnonneg : 0 ≤ᵐ[(volume : Measure (Submission.BoseGases.X S.card)).restrict
      (Submission.BoseGases.abox S.card ℓ)]
      (fun x : Submission.BoseGases.X S.card => (fibState S Ψ y x) ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have haesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X S.card => (fibState S Ψ y x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card ℓ)) :=
    (((contDiff_fibState S hΨ y).continuous.measurable).pow_const 2).aestronglyMeasurable
  -- (ii) the `ENNReal` box mass of the fibre, re-indexed by `slotIso S`
  have hlin : (∫⁻ x in Submission.BoseGases.abox S.card ℓ,
        ENNReal.ofReal ((fibState S Ψ y x) ^ 2))
      = ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
            (Submission.BoseGases.acube ℓ),
          ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2) := by
    rw [show Submission.BoseGases.abox S.card ℓ
        = Work.PerSector.slotBox (ι := Fin S.card) (Submission.BoseGases.acube ℓ)
        from rfl]
    refine Eq.trans (lintegral_congr (fun x => ?_))
      (lintegral_slotBox_slotIso S (Submission.BoseGases.acube_measurable ℓ)
        (fun z : Work.PerSector.SlotIn N S → ℝ³ =>
          ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)))
    rw [fibState_apply]
  rw [Work.BoseKinLoc.sqNormB,
    integral_eq_lintegral_of_nonneg_ae hnonneg haesm, hlin]
  rfl

/-- **The box mass of the fibre is integrable over the outside configurations.**  For a smooth state `Ψ` supported in the box `abox N L`, and any slot set `S`, the box mass `y ↦ sqNormB |S| ℓ (fibState S Ψ y)` of the fibre is integrable over the outside configurations `y` (coordinates in `acube (max L ℓ)`, outside `acube ℓ`).  This is the integrability needed to (i) convert the pointwise per-fibre bound into an integrated one and (ii) identify the sum of these integrals with the total squared norm.  It follows from Tonelli: the `y`-integral of the box mass of the fibre is the `abox N (max L ℓ)`-mass of the slot piece of `Ψ`, which is finite because `Ψ` is continuous with compact support (`Work.PerSector.slotMassENN_eq_fibre`, `Work.PerSector.slotMassENN_ne_top_of_ne_top`). -/
theorem integrable_sqNormB_fibState {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {L : ℝ} (S : Finset (Fin N))
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L) :
    MeasureTheory.IntegrableOn (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))
      (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (Submission.BoseGases.acube (max L ℓ) ∩ (Submission.BoseGases.acube ℓ)ᶜ)) := by
  classical
  have hΨc : Continuous Ψ := hΨ.continuous
  have hΨm : Measurable Ψ := hΨc.measurable
  -- The `ENNReal`-valued box mass of the fibre, as a function of the outside configuration.
  have hpoint : ∀ y : Work.PerSector.SlotOut N S → ℝ³,
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)
        = (∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)).toReal :=
    fun y => sqNormB_fibState_eq_slotFibreMassReal S hΨ y

  -- Measurability of the fibre mass in the outside configuration.
  have hmeas : AEMeasurable
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
            (Submission.BoseGases.acube ℓ),
          ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2))
      ((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
          (Submission.BoseGases.acube (max L ℓ) ∩ (Submission.BoseGases.acube ℓ)ᶜ))) :=
    ((measurable_lintegral_slotFibre S (Submission.BoseGases.acube_measurable ℓ)
      hΨm).aemeasurable).restrict

  -- Finiteness of the outside integral: Fubini (Tonelli) and the finiteness of the slot mass.
  have hne : (∫⁻ y in Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
        (Submission.BoseGases.acube (max L ℓ) ∩ (Submission.BoseGases.acube ℓ)ᶜ),
        ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
            (Submission.BoseGases.acube ℓ),
          ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)) ≠ ⊤ := by
    have hBL : Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube (max L ℓ) :=
      Submission.BoseGases.acube_mono (le_of_lt hℓ) (le_max_right L ℓ)
    have hfib := Work.PerSector.slotMassENN_eq_fibre (max L ℓ) S hBL
      (Submission.BoseGases.acube_measurable ℓ) hΨm
    change (∫⁻ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
        ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
            (Submission.BoseGases.acube ℓ),
          ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)) ≠ ⊤
    rw [← hfib]
    exact Work.PerSector.slotMassENN_ne_top_of_ne_top (max L ℓ)
      (Submission.BoseGases.acube ℓ) S Ψ
      (Work.FockBridge.sectorMassENN_ne_top_of_continuous (N := N) (L := max L ℓ) hΨc)

  rw [MeasureTheory.IntegrableOn]
  exact (MeasureTheory.integrable_toReal_of_lintegral_ne_top hmeas hne).congr
    (Filter.Eventually.of_forall (fun y => (hpoint y).symm))

end Work.BoseKinLoc.Sector
