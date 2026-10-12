import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.kinSectorSlotAdditive
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

noncomputable section

open MeasureTheory
open scoped Real BigOperators

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The excited-count (gap) half is slot-additive at the sector piece.**

For a state that is smooth and bounded on the analysis box, the `abox`-`L²`-mass of FS's
projection `Q_{B(u),i}` of the count-`k` sector piece is the sum of those of its slot pieces.  The
pointwise atom is `Work.PerSector.sq_boxQInd_eq_sum_sq_boxQInd_slotPiece` (evaluated at the sector
piece), and the only analytic input is the `abox`-integrability of each summand, which follows from
`Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn` once the slot pieces of the sector piece are
recognised as (bounded, measurable) indicator multiples of the state. -/
theorem cnSectorPiece_slotAdd {n : ℕ} {L d : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {Φ : Submission.BoseGases.X n → ℝ} {Cb : ℝ} (k : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hcd : ContDiff ℝ (⊤ : ENat) Φ) (hCb : 0 ≤ Cb)
    (hb : ∀ x ∈ Submission.BoseGases.abox n L, |Φ x| ≤ Cb) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n L,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ) x) ^ 2)
      = ∑ S : Finset (Fin n),
          ∫ x in Submission.BoseGases.abox n L,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S
                (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)) x) ^ 2 := by
  classical
  have hA : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hAa : Submission.BoseGases.dlBox L d u ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hvol : Work.SmallBoxSliding.boxMass L d u
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal L d u
  have hΦm : Measurable Φ := hcd.continuous.measurable
  -- the slot pieces of the state are bounded on the box by the state's bound
  have hbpiece : ∀ S : Finset (Fin n), ∀ x ∈ Submission.BoseGases.abox n L,
      |Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ x| ≤ Cb := by
    intro S x hx
    have h1 : |Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ x| ≤ |Φ x| := by
      simpa only [Real.norm_eq_abs, Work.PerSector.slotPiece] using
        (norm_indicator_le_norm_self
          (s := Work.PerSector.slotSet (Submission.BoseGases.dlBox L d u) S) (f := Φ) (a := x))
    exact le_trans h1 (hb x hx)
  -- integrability of each summand of the pointwise decomposition
  have hint : ∀ S : Finset (Fin n), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)) x) ^ 2)
      (Submission.BoseGases.abox n L) := by
    intro S
    by_cases hcard : S.card = k
    · rw [Work.PerSector.slotPiece_sectorPiece_eq_of_card_eq hcard Φ]
      exact Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn hA hAa hvol
        (Work.PerSector.slotPiece_measurable (Submission.BoseGases.dlBox L d u) hA S hΦm) hCb
        (hbpiece S) i
    · rw [Work.PerSector.slotPiece_sectorPiece_eq_zero_of_card_ne hcard Φ,
        Work.PerSector.boxQInd_zero]
      simp
  rw [show (∫ x in Submission.BoseGases.abox n L,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n L, ∑ S : Finset (Fin n),
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S
              (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)) x) ^ 2
      from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
        (fun x => Work.PerSector.sq_boxQInd_eq_sum_sq_boxQInd_slotPiece hA i x))]
  exact MeasureTheory.integral_finsetSum Finset.univ (fun S _ => hint S)

theorem sectorPieceWordAdditive {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {L d ε c μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n k : ℕ} {Cb : ℝ}
    (hL : 0 < L) (hd : 0 < d) {Φ : Submission.BoseGases.X n → ℝ}
    (hcd : ContDiff ℝ (⊤ : ENat) Φ) (hCb : 0 ≤ Cb)
    (hb : ∀ x ∈ Submission.BoseGases.abox n L, |Φ x| ≤ Cb)
    (hPotN : ∀ S : Finset (Fin n),
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ) x) ^ 2
          * (Submission.BoseGases.qLHSden n L μ (Submission.BoseGases.wSmallPair M L d u v)
              (Submission.BoseGases.wSmall1Pair h M L d u) x))
        (Submission.BoseGases.abox n L)) :
    Work.UBBInputs8.tBwordBInd n L d ε c u
        (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)
      + Work.SmallBoxSliding.qLHSwordB h M L d μ u
        (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)
    = ∑ S ∈ Finset.powersetCard k Finset.univ,
        (Work.UBBInputs8.tBwordBInd n L d ε c u
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
          + Work.SmallBoxSliding.qLHSwordB h M L d μ u
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) := by
  refine Work.PerSector.sectorPiece_slotWord_eq_sum_slotPiece h M k ?_ ?_ ?_
  · intro i
    exact cnSectorPiece_slotAdd k hL hd hcd hCb hb i
  · intro i
    exact Work.BoseFixB1B.kinSectorSlotAdditive k hL hd hcd i
  · intro S
    exact MeasureTheory.Integrable.congr (hPotN S)
      (Filter.Eventually.of_forall fun x => mul_comm _ _)

end

end Work.BoseFixB1B
