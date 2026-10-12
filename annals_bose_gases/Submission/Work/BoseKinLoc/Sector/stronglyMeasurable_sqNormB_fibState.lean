import Mathlib.Algebra.Order.Star.Real
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

/-!
# `Work.BoseKinLoc.Sector.stronglyMeasurable_sqNormB_fibState`

Strong measurability of the **box mass of the fibre** as a function of the outside configuration.

For a slot set `S : Finset (Fin N)`, a box width `ℓ` and a *measurable* state `Ψ : X N → ℝ`, the
fibre `fibState S Ψ y : X |S| → ℝ` (the `|S|`-particle state obtained by freezing the coordinates
outside `S` at `y`) has a box `L²`-mass `sqNormB |S| ℓ (fibState S Ψ y)`, and this module records
that the resulting function of `y` is `StronglyMeasurable` (indeed `Measurable`).

The proof is the pointwise form of Tonelli together with the `ENNReal` description of the box mass
of a nonnegative function:

* the `ENNReal`-valued fibre mass `y ↦ ∫⁻ z in (acube ℓ)^{S}, (Ψ (slotComb S z y))²` is measurable
  in `y` (`Work.BoseKinLoc.Sector.measurable_lintegral_slotFibre`), which uses only `Measurable Ψ`;
* the box mass `sqNormB |S| ℓ (fibState S Ψ y)` is the `toReal` of the *same* integral, written
  over the box `abox |S| ℓ` (via `integral_eq_lintegral_of_nonneg_ae`, then re-indexed by
  `slotIso S` with `Work.BoseKinLoc.Sector.lintegral_slotBox_slotIso`);
* `ENNReal.toReal` is measurable, and on `ℝ` a measurable function is strongly measurable.

This is the `ContDiff`-free (merely `Measurable Ψ`) strengthening of step 3 of
`Work.BoseKinLoc.Sector.integrable_sqNormB_fibStateA`, needed for the fibre decomposition of the
localised box form.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseKinLoc.Sector

set_option maxHeartbeats 1000000

/-- **The fibre of a measurable state is measurable in the configuration variable.**  The fibre is
`x ↦ Ψ (slotComb S (fun i ↦ x (slotIso S i)) y)`; the reassembly `(z, y) ↦ slotComb S z y` is
jointly measurable, hence so is its `z`-section, and re-indexing `x ↦ fun i ↦ x (slotIso S i)` is
measurable on the (finite) product of the configuration spaces. -/
theorem measurable_fibState {N : ℕ} (S : Finset (Fin N)) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Measurable Ψ) (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    Measurable (fibState S Ψ y) := by
  have hT : Measurable (fun x : Submission.BoseGases.X S.card =>
      (fun i : Work.PerSector.SlotIn N S => x (slotIso S i))) := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (slotIso S i)
  have hsec : Measurable (fun z : Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3) =>
      (z, y)) := measurable_id.prod measurable_const
  have hpair : Measurable (fun p : (Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3)) ×
      (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
      Ψ (Work.PerSector.slotComb S p.1 p.2)) :=
    Work.PerSector.measurable_slotFibre_pair S hΨ
  have hG : Measurable (fun z : Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3) =>
      Ψ (Work.PerSector.slotComb S z y)) := hpair.comp hsec
  exact hG.comp hT

theorem stronglyMeasurable_sqNormB_fibState {N : ℕ} (S : Finset (Fin N)) {ℓ : ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) :
    MeasureTheory.StronglyMeasurable (fun y : (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
      Work.BoseKinLoc.sqNormB S.card ℓ (Work.BoseKinLoc.Sector.fibState S Ψ y)) := by
  classical
  -- The `ENNReal`-valued fibre mass, as a function of the outside configuration.
  have hmeasL : Measurable (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
      ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
          (Submission.BoseGases.acube ℓ),
        ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)) :=
    measurable_lintegral_slotFibre S (Submission.BoseGases.acube_measurable ℓ) hΨ
  -- Pointwise: the box mass of the fibre is the `toReal` of that fibre mass.
  have hpoint : ∀ y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3),
      Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y)
        = (∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)).toReal := by
    intro y
    -- The `abox`-side `ENNReal` integral is the slot-side one, re-indexed by `slotIso S`.
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
          (fun z : Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3) =>
            ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)))
      rw [fibState_apply]
    have hnn : 0 ≤ᵐ[(volume : Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card ℓ)]
        (fun x : Submission.BoseGases.X S.card => (fibState S Ψ y x) ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg _)
    have haesm : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X S.card => (fibState S Ψ y x) ^ 2)
        ((volume : Measure (Submission.BoseGases.X S.card)).restrict
          (Submission.BoseGases.abox S.card ℓ)) :=
      ((measurable_fibState S hΨ y).pow_const 2).aestronglyMeasurable
    rw [Work.BoseKinLoc.sqNormB, integral_eq_lintegral_of_nonneg_ae hnn haesm, hlin]
  have hfun : (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.sqNormB S.card ℓ (fibState S Ψ y))
      = fun y => (∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S)
              (Submission.BoseGases.acube ℓ),
            ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)).toReal :=
    funext hpoint
  rw [hfun]
  exact (hmeasL.ennreal_toReal).stronglyMeasurable

end Work.BoseKinLoc.Sector
