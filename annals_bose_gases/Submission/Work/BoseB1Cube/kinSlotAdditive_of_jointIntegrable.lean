import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.kinSectorSlotAdditive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.kinSlotAdditive_of_jointIntegrable`

The abstract **slot additivity of the `p`-diagonal kinetic form**, stated for a bare measurable box
`A`, a continuous window `χ` supported in `A`, and a state `Φ` whose `fsKinCoeff`-weighted squared
amplitude energy of the box mean-free projection `Q_{A,i}Φ` is *jointly* `(p, x)`-integrable:

    ∫_p fsKinCoeff c ‖p‖ · (a³)⁻¹ ∫_{abox n a} ‖tBamp χ p (Q_{A,i} Φ) i x‖²
      = Σ_{S : Finset (Fin n)}
          ∫_p fsKinCoeff c ‖p‖ · (a³)⁻¹ ∫_{abox n a} ‖tBamp χ p (Q_{A,i} (slotPiece A S Φ)) i x‖² .

This is the cube-chapter companion of the corpus's private
`Work.BoseFixB1B.kinSlotAdditive_of_integrable`; it is also the interface needed by the
`Work.BoseB1Cube` slot-additivity threads at a general window.

## The argument (four steps, no decay estimate, no fibre-kernel integrability)

* **Pointwise Parseval over the slot sets** (`Work.PerSector.sum_tBamp_normSq_slotPiece`): at every
  configuration `x` the amplitudes of the `2^n` slot pieces of `Φ` add up in square to the
  amplitude of `Φ` itself, whence
  `‖tBamp χ p (Q_{A,i} Φ) i x‖² = Σ_S ‖tBamp χ p (Q_{A,i}(slotPiece A S Φ)) i x‖²`.
* **Joint integrability of each slot piece's energy** by domination via that identity (one summand
  of a sum of nonnegative terms), using the joint measurability
  `Work.BoseFixB1.measurable_tBamp_boxQInd_pair`.
* **Fubini** (`MeasureTheory.integral_prod`) on the product measure
  `volume × (volume.restrict (abox n a))`, plus the pull-out of the `p`-dependent coefficient.
* **`MeasureTheory.integral_finsetSum`** moves the finite sum over the `2^n` slot sets outside the
  `p`-integral, and the pointwise identity closes it.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem kinSlotAdditive_of_jointIntegrable {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ)
    (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≠ 0 → z ∈ A) {volA a c : ℝ} (ha : 0 < a)
    (i : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hint : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((a ^ 3)⁻¹ *
            ‖Work.SmallBoxTBWord.tBamp χ q.1
              (Work.UBBInputs8.boxQInd volA A i Φ) i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n a))))
    (hmeasS : ∀ S : Finset (Fin n), Measurable (Work.PerSector.slotPiece A S Φ)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ S : Finset (Fin n),
          ∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
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

end Work.BoseB1Cube
