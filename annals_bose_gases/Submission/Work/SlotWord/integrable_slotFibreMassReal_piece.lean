import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.integral_slotFibreMassReal_piece_eq_slotMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.integrable_slotFibreMassReal_piece`

**Integrability of the real fibre mass of a slot piece.**  For a measurable box `B ⊆ acube L` and a
measurable state `Φ` whose `abox N L`-`L²`-mass is finite, the real fibre mass
`y ↦ slotFibreMassReal B S (slotPiece B S Φ) y` is Bochner-integrable against the volume restricted
to the outside configurations `slotOutside L B S`.

This is the (R3)-bookkeeping for the fibre form of the slot-word residual: the corresponding
*identity* of integrals is `integral_slotFibreMassReal_piece_eq_slotMass`, and the same two inputs
which make that identity meaningful make the integrand itself integrable:

* the fibre mass is an *a.e. measurable* function of the outside configuration `y`
  (`PerSector.aemeasurable_slotFibreMass`, applied to the slot piece);
* the `y`-integral `∫⁻ y slotFibreMass B S (slotPiece B S Φ) y` is *finite*, because the
  `ENNReal`-Fubini identity `PerSector.slotMassENN_eq_fibre` identifies it with the slot mass
  `slotMassENN L B S (slotPiece B S Φ)`, and the slot mass of a slot piece is the slot mass of `Φ`
  (`slotMassENN_slotPiece_eq`), which is finite by `PerSector.slotMassENN_ne_top_of_ne_top`.

With measurability and finiteness of the `lintegral` in hand, `(g ·).toReal` is integrable by
`integrable_toReal_of_lintegral_ne_top`.
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

/-- **The `y`-integral of the fibre mass of a slot piece is finite.**  This is the finiteness input
of the integrability of the real fibre mass; it is exactly the finiteness of the slot mass
`slotMassENN L B S Φ`, transported to the fibre by Fubini (`slotMassENN_eq_fibre`) and by the
invariance of the slot mass under taking the slot piece (`slotMassENN_slotPiece_eq`). -/
theorem lintegral_slotFibreMass_slotPiece_ne_top (L : ℝ) {B : Set ℝ³} (S : Finset (Fin N))
    (hBL : B ⊆ acube L) (hB : MeasurableSet B) {Φ : X N → ℝ} (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    (∫⁻ y, Work.PerSector.slotFibreMass B S (Work.PerSector.slotPiece B S Φ) y
      ∂((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotOutside L B S))) ≠ ⊤ := by
  -- The slot piece is measurable, so the Fubini identity applies to it.
  have hpiece : Measurable (Work.PerSector.slotPiece B S Φ) :=
    Work.PerSector.slotPiece_measurable B hB S hΦ
  -- Fubini: the `y`-integral of the fibre mass is the slot mass of the piece.
  have hfib := Work.PerSector.slotMassENN_eq_fibre L S hBL hB hpiece
  have hkey : (∫⁻ y, Work.PerSector.slotFibreMass B S (Work.PerSector.slotPiece B S Φ) y
      ∂((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotOutside L B S)))
      = Work.PerSector.slotMassENN L B S (Work.PerSector.slotPiece B S Φ) := hfib.symm
  rw [hkey, slotMassENN_slotPiece_eq L B S Φ]
  exact Work.PerSector.slotMassENN_ne_top_of_ne_top L B S Φ hfin

theorem integrable_slotFibreMassReal_piece {N : ℕ} (L : ℝ)
    {B : Set (EuclideanSpace ℝ (Fin 3))} (S : Finset (Fin N))
    (hBL : B ⊆ Submission.BoseGases.acube L) (hB : MeasurableSet B)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.PerSector.slotFibreMassReal B S (Work.PerSector.slotPiece B S Φ) y)
      ((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L B S)) := by
  -- Measurability of the fibre mass as a function of the outside configuration.
  have hpiece : Measurable (Work.PerSector.slotPiece B S Φ) :=
    Work.PerSector.slotPiece_measurable B hB S hΦ
  have hmeas : AEMeasurable (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      Work.PerSector.slotFibreMass B S (Work.PerSector.slotPiece B S Φ) y)
      ((volume : Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotOutside L B S)) :=
    (Work.PerSector.aemeasurable_slotFibreMass hB S hpiece).restrict
  -- Finiteness of the `lintegral` of the fibre mass.
  have hne := lintegral_slotFibreMass_slotPiece_ne_top L S hBL hB hΦ hfin
  -- `(g ·).toReal` is integrable as soon as `g` is a.e. measurable with finite `lintegral`.
  exact integrable_toReal_of_lintegral_ne_top hmeas hne

end Work.SlotWord
