import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.contDiff_slotFibre
import Submission.Work.PerSector.measurable_slotFibre_pair
import Submission.Work.PerSector.slotMassENN_eq_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PerSector

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The fibre box mass is a measurable function of the outside configuration.**  This is the
"measurable field" half of the fibre decomposition: `y ↦ slotFibreMass B S Φ y` is the `k`-particle
box mass of the fibre, and it is `AEMeasurable` because the field `(z, y) ↦ Φ (slotComb S z y)` is
jointly measurable (`measurable_slotFibre_pair`) and the integral over `z ∈ B^{S}` is a partial
integral of a nonnegative jointly measurable function (Tonelli). -/
theorem aemeasurable_slotFibreMass {B : Set ℝ³} (hB : MeasurableSet B) (S : Finset (Fin N))
    {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    AEMeasurable (fun y : SlotOut N S → ℝ³ => slotFibreMass B S Φ y) volume := by
  -- The integrand `(z, y) ↦ ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2)` is jointly measurable.
  have hG : Measurable (fun p : (SlotIn N S → ℝ³) × (SlotOut N S → ℝ³) =>
      ENNReal.ofReal ((Φ (slotComb S p.1 p.2)) ^ 2)) :=
    ((measurable_slotFibre_pair S hΦ).pow_const 2).ennreal_ofReal
  -- Tonelli for nonnegative functions: the partial integral in `z` is measurable in `y`.
  have hmeas : Measurable (fun y : SlotOut N S → ℝ³ =>
      ∫⁻ z, ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2)
        ∂(volume.restrict (slotBox (ι := SlotIn N S) B))) :=
    hG.lintegral_prod_left'
  -- The restricted-set integral is the fibre mass, by definition.
  have hfun : (fun y : SlotOut N S → ℝ³ => slotFibreMass B S Φ y)
      = fun y => ∫⁻ z, ENNReal.ofReal ((Φ (slotComb S z y)) ^ 2)
          ∂(volume.restrict (slotBox (ι := SlotIn N S) B)) := by
    funext y
    rw [slotFibreMass]
  rw [hfun]
  exact hmeas.aemeasurable

end Work.PerSector

/-! ## Outer re-export

As in the neighbouring files of this chapter, the declaration proved above sits in the doubly nested
namespace produced by this file's header, so it is re-exported at the chapter's outer namespace
`Work.PerSector`. -/

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The fibre box mass is a measurable function of the outside configuration**, at the chapter's
outer namespace `Work.PerSector`. -/
theorem aemeasurable_slotFibreMass {B : Set ℝ³} (hB : MeasurableSet B) (S : Finset (Fin N))
    {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    AEMeasurable (fun y : SlotOut N S → ℝ³ => slotFibreMass B S Φ y) volume :=
  Work.PerSector.Work.PerSector.aemeasurable_slotFibreMass hB S hΦ

end Work.PerSector
