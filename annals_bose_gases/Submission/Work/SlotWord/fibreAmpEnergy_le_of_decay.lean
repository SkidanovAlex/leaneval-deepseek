import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
# `Work.SlotWord.fibreAmpEnergy_le_of_decay`

The **amplitude energy of a fibre slot is controlled by the pointwise decay of the amplitude**.

Recorded as the elementary measure-theoretic step of the (R3)-bookkeeping of the slot-word
chapter: if the windowed Fourier amplitude of the `j`-th fibre slot of the slot piece is
pointwise bounded by `C / (1 + ‖p‖)³` on the box `abox |S| L`, then its squared `L²`-norm over
that box — which is exactly `fibreAmpEnergy L d u S Φ e j p y` — is bounded by the square of the
pointwise bound times the volume of the box.

The proof is the trivial monotonicity of the Bochner integral: on the (finite measure, measurable)
box the integrand `z ↦ ‖tBamp … z‖²` is dominated by the constant `K²`, whence

  `∫ z in abox |S| L, ‖tBamp … z‖² ≤ K² * volume.real (abox |S| L)`.

The finiteness of the restricted box measure is `BoseGases.restrict_abox_eq_pi` (a product of
finite interval measures), so the constant is integrable.
-/

noncomputable section

open MeasureTheory

open scoped Real BigOperators ENNReal

namespace Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **A bounded squared norm on a finite box.**  If `‖f z‖ ≤ K` for all `z` in a measurable set
`s` of finite measure, then the integral of the squared norm of `f` over `s` is at most
`K ^ 2` times the volume of `s`. -/
private lemma setIntegral_normSq_le {k : ℕ} {s : Set (Submission.BoseGases.X k)}
    {E : Type*} [SeminormedAddCommGroup E]
    (hs : MeasurableSet s)
    [IsFiniteMeasure ((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s)]
    {f : Submission.BoseGases.X k → E} {K : ℝ}
    (hb : ∀ z ∈ s, ‖f z‖ ≤ K) :
    ∫ z in s, ‖f z‖ ^ 2
      ≤ K ^ 2 * (volume : MeasureTheory.Measure (Submission.BoseGases.X k)).real s := by
  have hK : Integrable (fun _ : Submission.BoseGases.X k => K ^ 2)
      ((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr inferInstance
  have hae : ∀ᵐ z ∂((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s),
      ‖f z‖ ^ 2 ≤ K ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => sq_nonneg (‖f z‖)) hK hae
  calc ∫ z in s, ‖f z‖ ^ 2
      = ∫ z, ‖f z‖ ^ 2
          ∂((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s) := rfl
    _ ≤ ∫ z, K ^ 2
          ∂((volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict s) := hmono
    _ = ∫ z in s, K ^ 2 := rfl
    _ = K ^ 2 * (volume : MeasureTheory.Measure (Submission.BoseGases.X k)).real s := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

theorem fibreAmpEnergy_le_of_decay {N : ℕ} (L d : ℝ) (hL : 0 < L)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ}
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) {C : ℝ}
    (hdec : ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3)
    (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
    {y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S) :
    Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y
      ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 *
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
            (Submission.BoseGases.abox S.card L) := by
  -- The restricted box measure is finite (a finite product of finite interval measures), so the
  -- constant `K ^ 2` is integrable on the box.
  have hboxFin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).restrict
        (Submission.BoseGases.abox S.card L)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    infer_instance
  rw [Work.SlotWord.fibreAmpEnergy]
  refine setIntegral_normSq_le
    (f := fun z => Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) j
          (Work.PerSector.slotFibreState S e
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j z)
    (Submission.BoseGases.abox_measurable S.card L) ?_
  intro z hz
  exact hdec j p y hy z hz

end Work.SlotWord
