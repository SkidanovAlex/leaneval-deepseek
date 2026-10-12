import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.aestronglyMeasurable_tBdiagFibreJoint
import Submission.Work.SlotWord.norm_tBdiagFibreJoint_le_of_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.integrable_tBdiagFibreJoint_of_decay`

**(R3) joint `(p,y)`-integrability of the spectral fibre integrand `tBdiagFibreJoint`.**

If the `p`-diagonal kinetic amplitude of the fibre
`slotFibreState S e (slotPiece B S Φ) y` decays like `C·(1+‖p‖)⁻³` uniformly in the outside
configuration `y ∈ slotOutside L (dlBox L d u) S` and in the box configuration `ζ ∈ abox |S| L`,
then

`(p, y) ↦ tBdiagFibreJoint L d u S Φ e (fsKinCoeff c) p y`

is Bochner integrable for `volume.prod (volume ↾ slotOutside L (dlBox L d u) S)`.

## The argument

Unfolding `tBdiagFibreJoint`,

  `tBdiagFibreJoint … p y = Σ_{j : Fin |S|} fsKinCoeff c ‖p‖ · ((L³)⁻¹ · fibreAmpEnergy j p y)`,

and `fibreAmpEnergy_le_of_decay` (with the *same* decay hypothesis) bounds the fibre amplitude
energy by `(C/(1+‖p‖)³)²` times the (finite) box volume `V`, uniformly in `j`, `p` and in the
outside configuration `y`.  Since every summand is nonnegative,

  `|tBdiagFibreJoint … p y| ≤ M · g p`,  `M := |S| · (L³)⁻¹ · V`,  `g p := fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²`.

The profile `g` is integrable on `ℝ³` (the `fsKinCoeff`-weighted decay profile, dominated by the
integrable `(1+‖p‖)⁻⁴`), hence so is `M · g p` for the product measure — the second factor
`volume ↾ slotOutside` is a *finite* measure (`volume_slotOutside_lt_top`), so
`Integrable.comp_fst` applies.  The joint a.e.-strong measurability is
`aestronglyMeasurable_tBdiagFibreJoint` (the fibre is `Φ` composed with the measurable slot
reassembly, `Q_{B,j}` is algebraic plus one parametric integral, `tBamp` one more), and
`Integrable.mono'` closes.
-/

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The `fsKinCoeff`-weighted decay profile is integrable on `ℝ³` -/

/-- The `fsKinCoeff`-weighted decay profile `p ↦ fsKinCoeff c ‖p‖ · (C/(1+‖p‖)³)²` is integrable:
the bound `fsKinCoeff c r ≤ (1+|c|)²(1+r)²` turns it into a multiple of `(1+‖p‖)⁻⁴`, and
`(1+‖·‖)⁻⁴` is integrable in dimension `3`. -/
theorem integrable_fsKinCoeff_decayLeb (c C : ℝ) :
    Integrable (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (C / (1 + ‖p‖) ^ 3) ^ 2) := by
  have hbase : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (r := (4 : ℝ)) (by
      rw [finrank_euclideanSpace_fin]; norm_num)
  have hg : Integrable (fun p : ℝ³ => (C ^ 2 * (1 + |c|) ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) :=
    hbase.const_mul _
  refine hg.mono' ?_ ?_
  · have h1 : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp
        continuous_norm
    have h2 : Continuous (fun p : ℝ³ => (C / (1 + ‖p‖) ^ 3) ^ 2) := by
      refine ((continuous_const.div ((continuous_const.add continuous_norm).pow 3) ?_)).pow 2
      intro p
      exact pow_ne_zero 3 (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖p‖))
    exact (h1.mul h2).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg _ _) (sq_nonneg _))]
    have hden : (0 : ℝ) < 1 + ‖p‖ := by positivity
    have hmax : (0 : ℝ) ≤ max (‖p‖ - c) 0 := le_max_right _ _
    have hle : max (‖p‖ - c) 0 ≤ (1 + |c|) * (1 + ‖p‖) := by
      have h2 : max (‖p‖ - c) 0 ≤ ‖p‖ + |c| := by
        refine max_le (by linarith [neg_le_abs c]) (by positivity)
      have h3 : ‖p‖ + |c| ≤ (1 + |c|) * (1 + ‖p‖) := by
        nlinarith [norm_nonneg p, abs_nonneg c, mul_nonneg (abs_nonneg c) (norm_nonneg p)]
      linarith
    have hsq : (max (‖p‖ - c) 0) ^ 2 ≤ ((1 + |c|) * (1 + ‖p‖)) ^ 2 :=
      pow_le_pow_left₀ hmax hle 2
    have hrpow : (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hden.le,
        Real.rpow_natCast]
    unfold Submission.BoseGases.fsKinCoeff
    rw [hrpow]
    calc (max (‖p‖ - c) 0) ^ 2 * (C / (1 + ‖p‖) ^ 3) ^ 2
        ≤ ((1 + |c|) * (1 + ‖p‖)) ^ 2 * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (C ^ 2 * (1 + |c|) ^ 2) * ((1 + ‖p‖) ^ 4)⁻¹ := by field_simp

/-! ## 3. The target -/

theorem integrable_tBdiagFibreJoint_of_decay {N : ℕ} (L d c : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    (hdec : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin S.card) (p : EuclideanSpace ℝ (Fin 3))
        (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)),
        y ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S →
        ∀ ζ ∈ Submission.BoseGases.abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) j
              (Work.PerSector.slotFibreState S e
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3) :
    MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) ×
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        Work.SlotWord.tBdiagFibreJoint L d u S Φ e (Submission.BoseGases.fsKinCoeff c) q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) := by
  obtain ⟨C, _hC0, hdec⟩ := hdec
  set s : Set (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :=
    Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S with hs
  have hsmeas : MeasurableSet s :=
    measurableSet_slotOutside L (measurableSet_dlBox L d u) S
  haveI hνfin : IsFiniteMeasure
      ((MeasureTheory.volume :
          MeasureTheory.Measure (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        s) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact volume_slotOutside_lt_top L hL.le (Submission.BoseGases.dlBox L d u) S⟩
  have hG : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * (C / (1 + ‖p‖) ^ 3) ^ 2) :=
    integrable_fsKinCoeff_decayLeb c C
  have hdom : Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) ×
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        ((S.card : ℝ) * ((L ^ 3)⁻¹ *
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
              (Submission.BoseGases.abox S.card L))))
          * (Submission.BoseGases.fsKinCoeff c ‖q.1‖ * (C / (1 + ‖q.1‖) ^ 3) ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))) :=
    (hG.const_mul ((S.card : ℝ) * ((L ^ 3)⁻¹ *
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X S.card)).real
          (Submission.BoseGases.abox S.card L))))).comp_fst _
  refine hdom.mono'
    (aestronglyMeasurable_tBdiagFibreJoint L d c u S hΦm e) ?_
  have hae : ∀ᵐ q ∂((MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
      ((MeasureTheory.volume :
          MeasureTheory.Measure (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S))),
      q.2 ∈ Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S := by
    rw [Measure.ae_prod_iff_ae_ae (hsmeas.preimage measurable_snd)]
    filter_upwards with a
    exact ae_restrict_mem hsmeas
  filter_upwards [hae] with q hq
  exact norm_tBdiagFibreJoint_le_of_decay L d c hL u S e hdec q.1 hq

end

end Work.SlotWord
