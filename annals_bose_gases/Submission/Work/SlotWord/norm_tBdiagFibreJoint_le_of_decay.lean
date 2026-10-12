import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.fibreAmpEnergy_le_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.norm_tBdiagFibreJoint_le_of_decay`

The **pointwise `(p,y)`-bound on the joint spectral fibre integrand**.

The joint integrand of the spectral fibre factorisation is a sum over the `|S|` slots,
`tBdiagFibreJoint … p y = Σ_{j : Fin |S|} fsKinCoeff c ‖p‖ · ((L³)⁻¹ · fibreAmpEnergy j p y)`,
and each fibre amplitude energy is dominated by `(C/(1+‖p‖)³)²` times the (finite) box volume
`V := |abox |S| L|` (`Work.SlotWord.fibreAmpEnergy_le_of_decay`, from the pointwise decay of the
windowed amplitude on the box).  As every summand is nonnegative (`fsKinCoeff` is a square, `L > 0`
and `fibreAmpEnergy` is an integral of a square), the triangle inequality for finite sums gives

`‖tBdiagFibreJoint … p y‖ ≤ |S| · ((L³)⁻¹·V) · (fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²)`.

This is the domination used to conclude the joint `(p,y)`-integrability of the spectral piece.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.SlotWord

theorem norm_tBdiagFibreJoint_le_of_decay {N : ℕ} (L d c : ℝ) (hL : 0 < L)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {C : ℝ}
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
    (p : EuclideanSpace ℝ (Fin 3))
    {y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S) :
    ‖Work.SlotWord.tBdiagFibreJoint L d u S Φ e (Submission.BoseGases.fsKinCoeff c) p y‖
      ≤ ((S.card : ℝ) * ((L ^ 3)⁻¹ *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L)))
          * (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by
  have hL3 : 0 < (L ^ 3)⁻¹ := by rw [inv_pos]; positivity
  have hF0 : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ :=
    Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖
  -- unfold the joint integrand into its slot sum
  rw [Work.SlotWord.tBdiagFibreJoint_eq]
  -- the pointwise bound on one summand
  have hterm : ∀ j : Fin S.card,
      ‖Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y)‖
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by
    intro j
    have hEj := fibreAmpEnergy_le_of_decay L d hL u S e hdec j p hy
    have hE0 : 0 ≤ Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y := by
      rw [Work.SlotWord.fibreAmpEnergy]
      exact integral_nonneg (fun z => sq_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg hF0 (mul_nonneg hL3.le hE0))]
    have h1 : Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y)
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEj hL3.le) hF0
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y)
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((L ^ 3)⁻¹ * ((C / (1 + ‖p‖) ^ 3) ^ 2 *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L))) := h1
      _ = (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring
  -- triangle inequality for the finite slot sum
  calc ‖∑ j : Fin S.card, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y)‖
      ≤ ∑ j : Fin S.card, ‖Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((L ^ 3)⁻¹ * Work.SlotWord.fibreAmpEnergy L d u S Φ e j p y)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin S.card,
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = (S.card : ℝ) *
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L) * (L ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    _ = ((S.card : ℝ) * ((L ^ 3)⁻¹ *
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L)))
          * (Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) := by ring

end Work.SlotWord
