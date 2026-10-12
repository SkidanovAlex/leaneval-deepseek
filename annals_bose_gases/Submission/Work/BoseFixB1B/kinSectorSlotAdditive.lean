import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.integrableOn_tBamp_sectorPiece_sq
import Submission.Work.BoseFixB1.integrable_prod_ampEnergy_sectorPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.kinSectorSlotAdditive`

The `p`-diagonal kinetic form of a **count-sector piece** is the sum of the same forms of its
**slot pieces**: the slot additivity of the spectral half of the small-box kinetic word *at the
sector piece* — the `hd` input consumed by
`Work.PerSector.sectorPiece_slotWord_eq_sum_slotPiece` (`hd` of
`Work.PerSector.perSectorBound_of_slotWordBound`).

## The argument

Everything is a *joint* `(p, x)`-integrability statement plus one pointwise Parseval identity; no
decay estimate and no fibre-kernel integrability is needed.

* **Pointwise Parseval over the slot sets** (`Work.PerSector.sum_tBamp_normSq_slotPiece`): at every
  configuration `x` at most one slot piece has a nonvanishing amplitude and it reproduces the
  amplitude of the state, hence
  `‖tBamp χ p (Q_{A,i}Ψ) i x‖² = Σ_S ‖tBamp χ p (Q_{A,i}(slotPiece A S Ψ)) i x‖²` — with the
  *sector piece* placed in the state slot `Ψ`.
* **Joint integrability of the state's energy**
  (`Work.BoseFixB1.integrable_prod_ampEnergy_sectorPiece`) and, by the Parseval inequality (one
  summand of a sum of nonnegative terms), of every slot piece's energy.
* **Fubini** (`MeasureTheory.integral_prod`) identifies the iterated integral with the product
  integral, and `MeasureTheory.integral_finsetSum` (finite sum over the `2^n` slot sets) moves the
  sum outside.  This is the `p`-space companion of the `x`-space argument of
  `Work.BoseFixB1.tBdiagFormInd_eq_sum_sectorPiece`, with the sectors replaced by the slot sets.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. The abstract additivity: Parseval + Fubini -/

/-- **Slot additivity of the `p`-diagonal kinetic form, from joint integrability.**  For a state
`Φ` whose `fsKinCoeff`-weighted squared amplitude energy is joint `(p, x)`-integrable, and every one
of whose slot pieces is measurable, the `p`-diagonal kinetic form of `Φ` is the sum over the slot
sets of the `p`-diagonal kinetic forms of the slot pieces.

The proof is (i) the pointwise Parseval identity `sum_tBamp_normSq_slotPiece`, (ii) joint
integrability of each slot piece's energy by domination (one summand of a sum of nonnegative terms),
(iii) `MeasureTheory.integral_prod` for both sides and (iv) `MeasureTheory.integral_finsetSum`. -/
private theorem kinSlotAdditive_of_integrable {n : ℕ} {A : Set E3} (hA : MeasurableSet A)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχ : ∀ z : E3, χ z ≠ 0 → z ∈ A)
    {volA a c : ℝ} (ha : 0 < a) (i : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hint : Integrable (fun q : E3 × Submission.BoseGases.X n =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((a ^ 3)⁻¹ *
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd volA A i Φ) i q.2‖ ^ 2))
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n a))))
    (hmeasS : ∀ S : Finset (Fin n), Measurable (Work.PerSector.slotPiece A S Φ)) :
    (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ S : Finset (Fin n),
          ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox n a,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i x‖ ^ 2) := by
  classical
  have ha3 : (0 : ℝ) ≤ (a ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg ha.le 3)
  -- ## (i) joint integrability of every slot piece's energy, by domination
  have hS_int : ∀ S : Finset (Fin n), Integrable (fun q : E3 × Submission.BoseGases.X n =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((a ^ 3)⁻¹ *
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i q.2‖ ^ 2))
      ((volume : Measure E3).prod
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n a))) := by
    intro S
    refine hint.mono' ?_ ?_
    · -- joint measurability of the slot piece's energy
      have hpair := Work.BoseFixB1.measurable_tBamp_boxQInd_pair (A := A) hA (χ := χ) hχc
        (volA := volA) (Ψ := Work.PerSector.slotPiece A S Φ) (hmeasS S) i
      have hcoef : Continuous (fun q : E3 × Submission.BoseGases.X n =>
          Submission.BoseGases.fsKinCoeff c ‖q.1‖) := by
        rw [show (fun q : E3 × Submission.BoseGases.X n =>
              Submission.BoseGases.fsKinCoeff c ‖q.1‖)
            = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘
                (fun q : E3 × Submission.BoseGases.X n => ‖q.1‖) from rfl]
        exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp
          (continuous_norm.comp continuous_fst)
      exact (hcoef.measurable.mul (hpair.const_mul ((a ^ 3)⁻¹))).aestronglyMeasurable
    · -- pointwise domination by the state's energy (Parseval: one summand of a nonnegative sum)
      refine Filter.Eventually.of_forall (fun q => ?_)
      have hle : ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i q.2‖ ^ 2
          ≤ ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd volA A i Φ) i q.2‖ ^ 2 := by
        rw [Work.PerSector.sum_tBamp_normSq_slotPiece (Φ := Φ) hA χ hχ i q.1 q.2]
        exact Finset.single_le_sum
          (fun S' _ => sq_nonneg (‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S' Φ)) i q.2‖))
          (Finset.mem_univ S)
      have hnn : (0 : ℝ) ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((a ^ 3)⁻¹ *
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i q.2‖ ^ 2) :=
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖q.1‖)
          (mul_nonneg ha3 (sq_nonneg _))
      rw [Real.norm_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle ha3)
        (Submission.BoseGases.fsKinCoeff_nonneg c ‖q.1‖)
  -- ## (ii) pull the `p`-dependent coefficient out of the `x`-integral
  have hpull : ∀ p : E3,
      (∫ x : Submission.BoseGases.X n, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n a)))
        = Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2) := by
    intro p
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hpullS : ∀ (S : Finset (Fin n)) (p : E3),
      (∫ x : Submission.BoseGases.X n, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i x‖ ^ 2)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n a)))
        = Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i x‖ ^ 2) := by
    intro S p
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- ## (iii) the pointwise identity `Σ_S (slot piece energy) = (state energy)`
  have hsum_eq : ∀ q : E3 × Submission.BoseGases.X n,
      (∑ S : Finset (Fin n), Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((a ^ 3)⁻¹ *
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i q.2‖ ^ 2))
        = Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((a ^ 3)⁻¹ *
          ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA A i Φ) i q.2‖ ^ 2) := by
    intro q
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      ← Work.PerSector.sum_tBamp_normSq_slotPiece hA χ hχ i q.1 q.2]
  -- ## (iv) Fubini on the product measure
  have hL : (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = ∫ q : E3 × Submission.BoseGases.X n, Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((a ^ 3)⁻¹ *
            ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA A i Φ) i q.2‖ ^ 2)
          ∂((volume : Measure E3).prod
            ((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n a))) :=
    (MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p => (hpull p).symm))).trans
      (MeasureTheory.integral_prod _ hint).symm
  have hS_eq : ∀ S : Finset (Fin n),
      (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i x‖ ^ 2))
        = ∫ q : E3 × Submission.BoseGases.X n, Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
            ((a ^ 3)⁻¹ *
              ‖Work.SmallBoxTBWord.tBamp χ q.1
                (Work.UBBInputs8.boxQInd volA A i (Work.PerSector.slotPiece A S Φ)) i q.2‖ ^ 2)
            ∂((volume : Measure E3).prod
              ((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n a))) := by
    intro S
    exact ((MeasureTheory.integral_prod _ (hS_int S)).trans
      (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (hpullS S)))).symm
  rw [hL, Finset.sum_congr rfl (fun S _ => hS_eq S),
    ← MeasureTheory.integral_finsetSum Finset.univ (fun S _ => hS_int S)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun q => (hsum_eq q).symm))

/-! ## 2. The target -/

theorem kinSectorSlotAdditive {n : ℕ} {L d c : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {Φ : Submission.BoseGases.X n → ℝ} (k : ℕ)
    (hL : 0 < L) (hd : 0 < d) (hcd : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin n) :
    (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n L,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)) i x‖ ^ 2))
      = ∑ S : Finset (Fin n),
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ * ((L ^ 3)⁻¹ *
            ∫ x in Submission.BoseGases.abox n L,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                  (Submission.BoseGases.dlBox L d u) i
                  (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S
                    (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ))) i x‖ ^ 2) := by
  classical
  have hA : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hχc : Continuous (Submission.BoseGases.chiB L d u) :=
    (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous
  have hχ : ∀ z : E3, Submission.BoseGases.chiB L d u z ≠ 0 →
      z ∈ Submission.BoseGases.dlBox L d u :=
    fun z hz => Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hL hd u (subset_tsupport _ hz)
  have hΨm : Measurable (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ) :=
    hcd.continuous.measurable.indicator
      (Work.FockBridge.sectorSet_measurable (Submission.BoseGases.dlBox L d u) hA k)
  have hmeasS : ∀ S : Finset (Fin n), Measurable (Work.PerSector.slotPiece
      (Submission.BoseGases.dlBox L d u) S
      (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox L d u) k Φ)) :=
    fun S => hΨm.indicator (Work.PerSector.slotSet_measurable _ hA S)
  exact kinSlotAdditive_of_integrable (A := Submission.BoseGases.dlBox L d u)
    (χ := Submission.BoseGases.chiB L d u) (volA := Work.SmallBoxSliding.boxMass L d u)
    (a := L) (c := c) hA hχc hχ hL i
    (Work.BoseFixB1.integrable_prod_ampEnergy_sectorPiece hL hd u hcd i k) hmeasS

end Work.BoseFixB1B
