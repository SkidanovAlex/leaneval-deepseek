import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.centreFibre_norm_eq
import Submission.Work.SlotWord.dlThreshold_le_diagWeBAt_of_smallbox
import Submission.Work.SlotWord.integrable_fibre_cnPlusBoxInd
import Submission.Work.SlotWord.integrable_fibre_qLHSword
import Submission.Work.SlotWord.integrable_slotFibreMassReal_piece
import Submission.Work.SlotWord.slotSplit_lintegral_slotBox
import Submission.Work.SlotWord.tBdiagFormInd_slotFibre
import Submission.Work.SlotWord.wSmall1Pair_support_left
import Submission.Work.SlotWord.wSmallPair_support_left
import Submission.Work.SlotWord.wordFibreFactorisation_of_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.aestronglyMeasurable_tBdiagFibreJoint`

The joint `(p, y)`-integrand of the spectral piece of the slot-word chapter,

  `(p, y) ↦ tBdiagFibreJoint L d u S Φ e (fsKinCoeff c) p y`

is a.e.-strongly-measurable for
`volume.prod (volume ↾ slotOutside L (dlBox L d u) S)`, for every **measurable** state `Φ`.

This is the measurability side condition consumed by the (R3) joint-integrability bookkeeping
`Work.SlotWord.integrable_tBdiagFibreJoint_of_decay`, and it is the joint analogue of
`Work.SlotWord.aestronglyMeasurable_fibre_tBdiagFormInd` (which is the same statement for the
`p`-integral, i.e. the `y`-only fibre function).

## The proof

`tBdiagFibreJoint … p y` is the finite sum over the fibre slots `i : Fin S.card` of

  `fsKinCoeff c ‖p‖ · ((L³)⁻¹ · ∫_{z ∈ abox |S| L} ‖tBamp χ_B p (Q_{B,i}(fibre_y)) i z‖²)`,

so it suffices that each summand is strongly measurable in `(p, y)`.  The joint `((p, y), z)`
integrand `‖tBamp χ_B p (Q_{B,i}(fibre_y)) i z‖²` is measurable by
`Work.SlotWord.measurable_tBamp_fibre` (the fibre is `Φ` composed with the measurable slot
reassembly, FS's box projection `Q_{B,i}` is algebraic plus one parametric integral, `tBamp` one
more), and the `z`-integral over `abox |S| L` is handled by
`StronglyMeasurable.integral_prod_right'`.  Multiplying by the (continuous, hence strongly
measurable) kinetic symbol `fsKinCoeff c ‖·‖` and summing the finitely many pieces gives the
conclusion.  A strongly measurable function is a.e.-strongly-measurable for *every* measure, so no
integrability or support condition is used.
-/

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- The FS spectral coefficient `r ↦ [r − c]₊²` is continuous. -/
private lemma continuous_fsKinCoeff_joint (c : ℝ) :
    Continuous (Submission.BoseGases.fsKinCoeff c) := by
  unfold Submission.BoseGases.fsKinCoeff
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

theorem aestronglyMeasurable_tBdiagFibreJoint {N : ℕ} (L d c : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) ×
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        Work.SlotWord.tBdiagFibreJoint L d u S Φ e (Submission.BoseGases.fsKinCoeff c) q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) := by
  have hA : MeasurableSet (dlBox L d u) := measurableSet_dlBox L d u
  have hΨ : Measurable (slotPiece (dlBox L d u) S Φ) := slotPiece_measurable _ hA S hΦm
  -- the box amplitude energy of the fibre is strongly measurable in `(p, y)`
  have hbox : ∀ i : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
            (boxQInd (boxMass L d u) (dlBox L d u) i
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) i z‖ ^ 2) := by
    intro i
    have hamp := measurable_tBamp_fibre L d u (boxMass L d u) (dlBox L d u) hA S e i hΨ
    have hnorm : Measurable (fun p : (ℝ³ × (SlotOut N S → ℝ³)) × X S.card =>
        ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p.1.1
          (boxQInd (boxMass L d u) (dlBox L d u) i
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) p.1.2)) i p.2‖ ^ 2) :=
      hamp.norm.pow_const 2
    exact hnorm.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (X S.card)).restrict (abox S.card L))
  -- the kinetic symbol
  have hkin : StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => Submission.BoseGases.fsKinCoeff c ‖q.1‖) :=
    ((continuous_fsKinCoeff_joint c).measurable.comp continuous_fst.norm.measurable).stronglyMeasurable
  -- the joint `(p, y)`-integrand of the `i`-th summand
  have hjoint : ∀ i : Fin S.card, StronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((L ^ 3)⁻¹ *
          ∫ z in abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
              (boxQInd (boxMass L d u) (dlBox L d u) i
                (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) i z‖ ^ 2)) := by
    intro i
    exact hkin.mul ((hbox i).const_mul _)
  -- the sum over the fibre slots
  have hsum : StronglyMeasurable
      (∑ i : Fin S.card, (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((L ^ 3)⁻¹ *
          ∫ z in abox S.card L,
            ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
              (boxQInd (boxMass L d u) (dlBox L d u) i
                (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) i z‖ ^ 2))) :=
    Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hjoint i)
  convert hsum.aestronglyMeasurable using 1
  funext q
  simp only [Finset.sum_apply, tBdiagFibreJoint, pieceFibre]

end

end Work.SlotWord
