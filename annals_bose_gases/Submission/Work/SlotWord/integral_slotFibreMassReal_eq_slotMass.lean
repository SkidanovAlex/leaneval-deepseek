import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.integral_slotFibreMassReal_eq_slotMass`

**The real fibre decomposition of a slot mass.**  For a measurable box `B ⊆ acube L` and a
measurable state `Φ` whose `abox N L`-`L²`-mass is finite, the integral over the *outside*
configurations `y ∈ slotOutside L B S` of the (real) box mass of the fibre `z ↦ Φ (slotComb S z y)`
equals the real slot mass `slotMass L B S Φ = (∫⁻_{abox} 1_{slotSet B S}·Φ²).toReal`.

The `ENNReal`-level Fubini identity is `PerSector.slotMassENN_eq_fibre`; the passage to the real
Bochner integral is `integral_toReal`, whose two side conditions are supplied by
`PerSector.aemeasurable_slotFibreMass` (the fibre mass is a measurable function of `y`) and by the
finiteness of the slot mass `PerSector.slotMassENN_ne_top_of_ne_top` coming from `hfin`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

theorem integral_slotFibreMassReal_eq_slotMass {N : ℕ} (L : ℝ)
    {B : Set (EuclideanSpace ℝ (Fin 3))} (S : Finset (Fin N))
    (hBL : B ⊆ Submission.BoseGases.acube L) (hB : MeasurableSet B)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    ∫ y in Work.PerSector.slotOutside L B S, Work.PerSector.slotFibreMassReal B S Φ y
      = Work.PerSector.slotMass L B S Φ := by
  -- The `ENNReal` Fubini identity: the slot mass is the `y`-integral of the fibre mass.
  have hfib : Work.PerSector.slotMassENN L B S Φ
      = ∫⁻ y in Work.PerSector.slotOutside L B S, Work.PerSector.slotFibreMass B S Φ y :=
    Work.PerSector.slotMassENN_eq_fibre L S hBL hB hΦ
  -- Finiteness of that `y`-integral, inherited from `hfin` through the slot mass.
  have hne : (∫⁻ y in Work.PerSector.slotOutside L B S,
      Work.PerSector.slotFibreMass B S Φ y) ≠ ⊤ := by
    rw [← hfib]
    exact Work.PerSector.slotMassENN_ne_top_of_ne_top L B S Φ hfin
  -- Measurability of the fibre mass as a function of the outside configuration.
  have hmeas : AEMeasurable (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      Work.PerSector.slotFibreMass B S Φ y)
      ((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotOutside L B S)) :=
    (Work.PerSector.aemeasurable_slotFibreMass hB S hΦ).restrict
  -- `integral_toReal`: a.e. finiteness of the fibre mass, from a finite lintegral.
  have hlt : ∀ᵐ y ∂((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
      (Work.PerSector.slotOutside L B S)), Work.PerSector.slotFibreMass B S Φ y < ⊤ :=
    ae_lt_top' hmeas hne
  rw [Work.PerSector.slotMass, hfib]
  rw [show (∫ y in Work.PerSector.slotOutside L B S,
        Work.PerSector.slotFibreMassReal B S Φ y)
      = ∫ y, (Work.PerSector.slotFibreMass B S Φ y).toReal
          ∂((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
            (Work.PerSector.slotOutside L B S)) from rfl]
  exact integral_toReal hmeas hlt

end Work.SlotWord
