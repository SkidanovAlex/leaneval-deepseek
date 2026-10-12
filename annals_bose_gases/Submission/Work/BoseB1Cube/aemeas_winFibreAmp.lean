import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.aemeasurable_fibreAmpEnergy
import Submission.Work.SlotWord.measurable_boxQInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.aemeas_winFibreAmp`

The fibre amplitude energy

`q ↦ ∫_{abox |S| L} ‖tBamp χ q.1 (Q_{B(u),j} (fibre of the slot piece at q.2)) j z‖²`

is a.e.-strongly-measurable for the product of Lebesgue measure on the sliding centre `q.1` and
Lebesgue measure on the outside configurations `q.2`, restricted to the outside set `slotOutside`.

This is the *measurable-window* refinement of `Work.SlotWord.aemeasurable_fibreAmpEnergy`, which is
stated for the concrete continuous window `chiB L d u` and a **continuous** state `Φ`.  Here the
window `χ` is an arbitrary measurable function of the space variable and the state is only assumed
**measurable**.  Nothing in the argument needs continuity: the chain

* the fibre `(y, z) ↦ slotFibreState S e Φ y z` is jointly measurable because it is `Φ` composed
  with the (measurable) slot reassembly;
* FS's box projection `Q_{B,j}` — an algebraic expression in `Ψ` together with *one* parametric
  integral over the box `B` — preserves joint measurability;
* the windowed amplitude `tBamp χ p ·` — *one* parametric integral over `ℝ³` — again preserves it,

uses measurability only.  The final `z`-integral over `abox` is handled with
`StronglyMeasurable.integral_prod_right'`, after which `Measurable` gives `AEStronglyMeasurable`
for any measure.
-/

namespace Work.BoseB1Cube

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The windowed amplitude of the fibre is jointly measurable (measurable window) -/

theorem measurable_tBamp_fibre_meas (χ : ℝ³ → ℝ) (hχm : Measurable χ)
    (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card) (j : Fin S.card)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun p : (ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card =>
      Work.SmallBoxTBWord.tBamp χ p.1.1
        (Work.UBBInputs8.boxQInd volA A j
          (Work.PerSector.slotFibreState S e Φ p.1.2)) j p.2) := by
  classical
  have hboxQ := Work.SlotWord.measurable_boxQInd_fibre volA A hA S e j hΦ
  -- joint measurability of the amplitude integrand
  have hupd2 : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        (q.1.2, q.2)) :=
    Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd
  have hupd : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        Function.update q.1.2 j q.2) :=
    (measurable_update' (X := fun _ : Fin S.card => ℝ³) (a := j)).comp hupd2
  have hboxQw : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        Work.UBBInputs8.boxQInd volA A j
          (Work.PerSector.slotFibreState S e Φ q.1.1.2) (Function.update q.1.2 j q.2)) :=
    hboxQ.comp (Measurable.prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)) hupd)
  have hinner : Continuous
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        (inner ℝ q.1.1.1 q.2 : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Continuous.inner (continuous_fst.comp (continuous_fst.comp continuous_fst)) continuous_snd)
  have h1 : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        (χ q.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hχm.comp measurable_snd)
  have h2 : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner).neg)).measurable
  have h3 : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        ((Work.UBBInputs8.boxQInd volA A j
          (Work.PerSector.slotFibreState S e Φ q.1.1.2)
          (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hboxQw
  have hJ : Measurable
      (fun q : ((ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card) × ℝ³ =>
        (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ))) *
          ((Work.UBBInputs8.boxQInd volA A j
            (Work.PerSector.slotFibreState S e Φ q.1.1.2)
            (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    (h1.mul h2).mul h3
  have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  convert hSM.measurable using 1
  funext p
  simp only [Work.SmallBoxTBWord.tBamp]

/-! ## 2. The target -/

theorem aemeas_winFibreAmp {N : ℕ} (L d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχm : Measurable χ) (j : Fin S.card) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        ∫ z in Submission.BoseGases.abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) j z‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hΨ : Measurable
      (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) :=
    Work.PerSector.slotPiece_measurable (Submission.BoseGases.dlBox L d u) hA S hΦ
  have hamp := measurable_tBamp_fibre_meas χ hχm (Work.SmallBoxSliding.boxMass L d u)
    (Submission.BoseGases.dlBox L d u) hA S e j hΨ
  have hnorm : Measurable
      (fun p : (ℝ³ × (Work.PerSector.SlotOut N S → ℝ³)) × Submission.BoseGases.X S.card =>
        ‖Work.SmallBoxTBWord.tBamp χ p.1.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) j
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) p.1.2)) j p.2‖ ^ 2) :=
    hamp.norm.pow_const 2
  have hSM := hnorm.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card L))
  have hfin : Measurable (fun q : ℝ³ × (Work.PerSector.SlotOut N S → ℝ³) =>
      ∫ z in Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) j
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) q.2)) j z‖ ^ 2) :=
    hSM.measurable
  exact hfin.aestronglyMeasurable

end

end Work.BoseB1Cube
