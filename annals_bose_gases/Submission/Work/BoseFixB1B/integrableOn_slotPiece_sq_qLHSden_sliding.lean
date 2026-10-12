import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.integrable_qLHSden_regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden_sliding`

The dilute-regime integrability of the **slot-piece** weighted `qLHSword` diagonal density

  `x ↦ (slotPiece B S (sectorPiece B k Φ) x)² · qLHSden n ℓ μ (wSmallPair M ℓ d u v)
              (wSmall1Pair h M ℓ d u) x`

over the centred box `abox n ℓ`, where `B = dlBox ℓ d u` is the sliding small box.

The unweighted density is integrable under the paper's regime
(`Work.BoseFixB1B.integrable_qLHSden_regime`: the one-body fibres are uniformly bounded by
`Work.BoseFixB1B.w1Fibre_bdd` and the two-body slots by `Work.BoseFixB1.integrableOn_slot_wSmallPair`).
The weight is the square of the slot piece of the sector piece, i.e. an indicator function times
`Φ`, hence measurable and bounded on the box by `Cb`, so multiplying preserves integrability
(`MeasureTheory.Integrable.bdd_mul`). This is the `slotPiece (sectorPiece ·)` analogue of
`Work.BoseFixB1.integrableOn_sectorPiece_sq_qLHSden_regime`.
-/

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real BigOperators

open Submission.BoseGases
open Work.PerSector Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem integrableOn_slotPiece_sq_qLHSden_sliding {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} {ℓ d μ R0 : ℝ}
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hv1 : MeasureTheory.MemLp v 1) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hdR : R0 ≤ ℓ * d / 16) (hdRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n k : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ Cb) (S : Finset (Fin n)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox ℓ d u) S
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x) ^ 2
          * Submission.BoseGases.qLHSden n ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
      (Submission.BoseGases.abox n ℓ) := by
  classical
  -- ## 1. The unweighted density is integrable over the box under the regime
  have hden : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.qLHSden n ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) x) (Submission.BoseGases.abox n ℓ) :=
    integrable_qLHSden_regime (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d) (μ := μ) (R0 := R0)
      hM hℓ hd hv1 hR0 hv_supp hdR hdRχ u (k := n)
  -- ## 2. The weight `(slotPiece (sectorPiece))²` is measurable
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hΨm : Measurable (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) :=
    hΦ.measurable.indicator
      (FockBridge.sectorSet_measurable (Submission.BoseGases.dlBox ℓ d u) hA k)
  have hWm : Measurable (slotPiece (Submission.BoseGases.dlBox ℓ d u) S
      (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) :=
    slotPiece_measurable (Submission.BoseGases.dlBox ℓ d u) hA S hΨm
  -- ## 3. The weight is bounded by `Cb` on the box
  have hWb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |slotPiece (Submission.BoseGases.dlBox ℓ d u) S
        (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x| ≤ Cb := by
    intro x hx
    by_cases hxs : x ∈ slotSet (Submission.BoseGases.dlBox ℓ d u) S
    · rw [slotPiece, Set.indicator_of_mem hxs]
      by_cases hxsec : x ∈ sectorSet (Submission.BoseGases.dlBox ℓ d u) k
      · rw [sectorPiece, Set.indicator_of_mem hxsec]
        exact hb x hx
      · rw [sectorPiece, Set.indicator_of_notMem hxsec, abs_zero]
        exact hCb
    · rw [slotPiece, Set.indicator_of_notMem hxs, abs_zero]
      exact hCb
  have hW2m : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        (slotPiece (Submission.BoseGases.dlBox ℓ d u) S
          (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x) ^ 2)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    (hWm.pow_const 2).aestronglyMeasurable
  have hW2b : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖(slotPiece (Submission.BoseGases.dlBox ℓ d u) S
          (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x) ^ 2‖ ≤ Cb ^ 2 := by
    filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (slotPiece (Submission.BoseGases.dlBox ℓ d u) S
            (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x) ^ 2
        = |slotPiece (Submission.BoseGases.dlBox ℓ d u) S
            (sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x| ^ 2 := (sq_abs _).symm
      _ ≤ Cb ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hWb x hx) 2
  -- ## 4. Multiply the integrable density by the bounded measurable weight
  exact hden.bdd_mul hW2m hW2b

end Work.BoseFixB1B
