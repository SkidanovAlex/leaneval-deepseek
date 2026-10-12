import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.integral_slotFibreMassReal_eq_slotMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.integral_slotFibreMassReal_piece_eq_slotMass`

**The real fibre decomposition of the slot mass of a slot piece.**  For a measurable box
`B ⊆ acube L` and a measurable state `Φ` whose `abox N L`-`L²`-mass is finite, the integral over
the *outside* configurations `y ∈ slotOutside L B S` of the (real) box mass of the fibre
`z ↦ slotPiece B S Φ (slotComb S z y)` equals the real slot mass
`slotMass L B S Φ = (∫⁻_{abox} 1_{slotSet B S}·Φ²).toReal`.

The point is that the slot piece is *again* a state to which the fibre decomposition applies: its
`abox`-mass is exactly the slot mass `slotMassENN L B S Φ`, so it is finite as soon as the mass of
`Φ` is (`PerSector.slotMassENN_ne_top_of_ne_top`), and its *slot* mass is the slot mass of `Φ`.
The identity itself is then `integral_slotFibreMassReal_eq_slotMass` at `Φ := slotPiece B S Φ`,
whose two side conditions are measurability of the piece (`PerSector.slotPiece_measurable`) and
the two mass computations just described.
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

/-- **The pointwise square of a slot piece.**  Squaring the slot piece kills the part of the state
outside the slot set, so `ENNReal.ofReal ((slotPiece B S Φ x)²)` is the indicator of the slot set
applied to `ENNReal.ofReal ((Φ x)²)`.  This is `PerSector.slotPiece_sq` under `ofReal`, with the
indicator pulled out. -/
theorem ennreal_ofReal_slotPiece_sq (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (x : X N) :
    ENNReal.ofReal ((Work.PerSector.slotPiece B S Φ x) ^ 2)
      = (Work.PerSector.slotSet B S).indicator
          (fun y => ENNReal.ofReal ((Φ y) ^ 2)) x := by
  by_cases hx : x ∈ Work.PerSector.slotSet B S
  · rw [Set.indicator_of_mem hx]
    have : Work.PerSector.slotPiece B S Φ x = Φ x := by
      rw [Work.PerSector.slotPiece, Set.indicator_of_mem hx]
    rw [this]
  · rw [Set.indicator_of_notMem hx]
    have : Work.PerSector.slotPiece B S Φ x = 0 := by
      rw [Work.PerSector.slotPiece, Set.indicator_of_notMem hx]
    rw [this]
    simp

/-- **The `abox`-mass of a slot piece is the slot mass of the state.**  Integrating the pointwise
square identity: `∫⁻_{abox} (slotPiece B S Φ)² = slotMassENN L B S Φ`. -/
theorem lintegral_slotPiece_sq_eq_slotMassENN (L : ℝ) (B : Set ℝ³)
    (S : Finset (Fin N)) (Φ : X N → ℝ) :
    (∫⁻ x in abox N L, ENNReal.ofReal ((Work.PerSector.slotPiece B S Φ x) ^ 2))
      = Work.PerSector.slotMassENN L B S Φ := by
  rw [Work.PerSector.slotMassENN]
  exact lintegral_congr (fun x => ennreal_ofReal_slotPiece_sq B S Φ x)

/-- **The slot mass of a slot piece is the slot mass of the state**: restricting a state to its own
slot set and then restricting again to that slot set changes nothing. -/
theorem slotMassENN_slotPiece_eq (L : ℝ) (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) :
    Work.PerSector.slotMassENN L B S (Work.PerSector.slotPiece B S Φ)
      = Work.PerSector.slotMassENN L B S Φ := by
  rw [Work.PerSector.slotMassENN, Work.PerSector.slotMassENN]
  refine lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ Work.PerSector.slotSet B S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rw [Work.PerSector.slotPiece, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem integral_slotFibreMassReal_piece_eq_slotMass {N : ℕ} (L : ℝ)
    {B : Set (EuclideanSpace ℝ (Fin 3))} (S : Finset (Fin N))
    (hBL : B ⊆ Submission.BoseGases.acube L) (hB : MeasurableSet B)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ)
    (hfin : (∫⁻ x in Submission.BoseGases.abox N L, ENNReal.ofReal ((Φ x) ^ 2)) ≠ ⊤) :
    ∫ y in Work.PerSector.slotOutside L B S,
        Work.PerSector.slotFibreMassReal B S
          (Work.PerSector.slotPiece B S Φ) y
      = Work.PerSector.slotMass L B S Φ := by
  -- The slot piece is measurable.
  have hpiece : Measurable (Work.PerSector.slotPiece B S Φ) :=
    Work.PerSector.slotPiece_measurable B hB S hΦ
  -- Its `abox`-mass is the slot mass `m_S`, hence finite by `hfin`.
  have hfin_piece : (∫⁻ x in Submission.BoseGases.abox N L,
      ENNReal.ofReal ((Work.PerSector.slotPiece B S Φ x) ^ 2)) ≠ ⊤ := by
    rw [lintegral_slotPiece_sq_eq_slotMassENN L B S Φ]
    exact Work.PerSector.slotMassENN_ne_top_of_ne_top L B S Φ hfin
  -- The slot mass of the piece is the slot mass of the state.
  have hmass : Work.PerSector.slotMass L B S (Work.PerSector.slotPiece B S Φ)
      = Work.PerSector.slotMass L B S Φ := by
    rw [Work.PerSector.slotMass, Work.PerSector.slotMass, slotMassENN_slotPiece_eq L B S Φ]
  -- The fibre decomposition for the piece, then the identification of the masses.
  exact (integral_slotFibreMassReal_eq_slotMass L S hBL hB hpiece hfin_piece).trans hmass

end Work.SlotWord
