import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.FibreResidual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Sector.measurable_lintegral_slotFibre`

Measurability of the *fibre box mass as a function of the outside configuration*.

For a box `B ⊆ ℝ³`, a slot set `S : Finset (Fin N)` and a measurable state `Ψ : X N → ℝ`, the
outside-integrals of the Fubini decomposition (`Work.PerSector.slotMassENN_eq_fibre`) are taken
against the field

    y ↦ ∫⁻ z in slotBox (ι := SlotIn N S) B, ENNReal.ofReal ((Ψ (slotComb S z y)) ^ 2),

i.e. the `B^{S}`-mass of the fibre `z ↦ Ψ (slotComb S z y)`.  This module records that this field is
an honest *measurable* function of `y` (not merely `AEMeasurable`: the pointwise-integral form of
Tonelli gives measurability outright; compare `Work.PerSector.aemeasurable_slotFibreMass`, which is
the `AEMeasurable` reading of the same fact).

The proof is the pointwise form of Tonelli: the integrand
`(z, y) ↦ ENNReal.ofReal ((Ψ (slotComb S z y)) ^ 2)` is jointly measurable because reassembling a
configuration from its in-box and outside slot coordinates is measurable
(`Work.PerSector.measurable_slotFibre_pair`), and the partial integral of a nonnegative jointly
measurable function in one variable of a product is measurable
(`Measurable.lintegral_prod_left'`).  Note that no measurability of the box `B` is needed — an
integral over an arbitrary set is a partial integral against the restricted measure.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseKinLoc.Sector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The fibre box mass is a measurable function of the outside configuration** (pointwise Tonelli).

The field `y ↦ ∫⁻ z in B^{S}, (Ψ (slotComb S z y))²` over the outside configurations
`y : SlotOut N S → ℝ³` is measurable for a measurable state `Ψ : X N → ℝ`.

This is the measurability input needed to apply Tonelli/Fubini to the outside integral of the
fibre decomposition, and it is stated in the *pointwise* (`Measurable`, not `AEMeasurable`) form
used there. -/
theorem measurable_lintegral_slotFibre {N : ℕ} (S : Finset (Fin N)) {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : MeasurableSet B) {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
      ∫⁻ z in Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B,
        ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S z y)) ^ 2)) := by
  -- The integrand `(z, y) ↦ ENNReal.ofReal ((Ψ (slotComb S z y)) ^ 2)` is jointly measurable.
  have hG : Measurable (fun p : (Work.PerSector.SlotIn N S → ℝ³) ×
      (Work.PerSector.SlotOut N S → ℝ³) =>
      ENNReal.ofReal ((Ψ (Work.PerSector.slotComb S p.1 p.2)) ^ 2)) :=
    ((Work.PerSector.measurable_slotFibre_pair S hΨ).pow_const 2).ennreal_ofReal
  -- Tonelli, pointwise form: the partial integral in `z` (against the restriction to the box
  -- `slotBox B`, which is `∫⁻ z in slotBox B, ·` by definition) is measurable in `y`.
  exact hG.lintegral_prod_left'
    (μ := volume.restrict (Work.PerSector.slotBox (ι := Work.PerSector.SlotIn N S) B))

end Work.BoseKinLoc.Sector
