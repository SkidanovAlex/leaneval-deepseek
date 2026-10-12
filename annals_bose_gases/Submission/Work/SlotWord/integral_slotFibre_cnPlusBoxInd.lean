import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.SlotFibreInfra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.integral_slotFibre_cnPlusBoxInd`

**The fibre factorisation of the box excited count `n₊`.**  For a slot set `S : Finset (Fin N)`,
a bijection `e : SlotIn N S ≃ Fin S.card`, an outside configuration
`y : SlotOut N S → ℝ³` and a state `Φ : X N → ℝ`, the `N`-particle excited count of the slot piece
`slotPiece A S Φ`, evaluated at the reassembled configuration
`slotComb S (ζ ∘ e) y`, is the `S.card`-particle excited count of the transported fibre
`slotFibreState S e (slotPiece A S Φ) y`.

The mathematical content is a reindexing.  The projection `Q_{A,j}` of the slot piece vanishes
identically when `j ∉ S` (`boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet`: the shift set of
`Q_{A,j}` requires `j ∈ S`), and for `j ∈ S` the sum over `j` reindexes along the bijection `e` to
the sum over the `S.card` slots of the fibre.  The fibre identification of each summand is
`boxQInd_slotFibreState` (`SlotFibreInfra`), and the exchange of the finite sum with the Bochner
integral uses the integrability hypothesis `hInt`.
-/

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem integral_slotFibre_cnPlusBoxInd {N : ℕ} (L : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hAL : A ⊆ Submission.BoseGases.acube L) (volA : ℝ)
    (S : Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ)
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))
    (hInt : ∀ i : Fin S.card, MeasureTheory.IntegrableOn
      (fun ζ => (Work.UBBInputs8.boxQInd volA A i
        (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Φ) y) ζ)^2)
      (Submission.BoseGases.abox S.card L)) :
    ∫ ζ in Submission.BoseGases.abox S.card L,
        (∑ j : Fin N, (Work.UBBInputs8.boxQInd volA A j (Work.PerSector.slotPiece A S Φ)
            (Work.PerSector.slotComb S (fun k : Work.PerSector.SlotIn N S => ζ (e k)) y))^2)
      = Work.UBBInputs8.cnPlusBoxInd L A volA
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Φ) y) := by
  classical
  set Ψ : X N → ℝ := slotPiece A S Φ with hΨ
  -- **Step 1.**  Pointwise, the `N`-fold sum of projected squares collapses to the `S.card`-fold
  -- sum of the fibre: the `j ∉ S` summands vanish, and the `j ∈ S` summands reindex along `e`.
  have hpt : ∀ ζ : X S.card,
      (∑ j : Fin N, (boxQInd volA A j Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2)
        = ∑ i : Fin S.card,
            (boxQInd volA A (e.symm i).1 Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2 := by
    intro ζ
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => ?_)]
    · rw [← Finset.sum_attach S (fun j =>
          (boxQInd volA A j Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2)]
      rw [← Finset.univ_eq_attach S]
      exact (Equiv.sum_comp e.symm (fun j : SlotIn N S =>
        (boxQInd volA A j.1 Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2)).symm
    · have hnot : slotComb S (fun k : SlotIn N S => ζ (e k)) y ∉ slotShiftSet A S j :=
        fun h => hj h.1
      rw [boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet hA j S hnot]
      ring
  -- **Step 2.**  Integrability of each summand of the reindexed sum, transported from `hInt`
  -- along `boxQInd_slotFibreState`.
  have hInt' : ∀ i : Fin S.card, IntegrableOn
      (fun ζ : X S.card => (boxQInd volA A (e.symm i).1 Ψ
        (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2) (abox S.card L) := by
    intro i
    have hcongr : (fun ζ : X S.card => (boxQInd volA A i (slotFibreState S e Ψ y) ζ)^2)
        = fun ζ : X S.card => (boxQInd volA A (e.symm i).1 Ψ
            (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2 := by
      funext ζ
      exact congrArg (·^2) (boxQInd_slotFibreState e volA A Ψ i ζ y)
    rw [← hcongr]
    exact hInt i
  -- **Step 3.**  The exchange of the finite sum with the Bochner integral.
  have key : (∫ ζ in abox S.card L,
        (∑ j : Fin N, (boxQInd volA A j Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2))
      = ∑ i : Fin S.card, ∫ ζ in abox S.card L,
          (boxQInd volA A (e.symm i).1 Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y))^2 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hInt' i)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ζ => hpt ζ))
  rw [key]
  -- **Step 4.**  Unfolding `cnPlusBoxInd` and identifying each summand with the fibre.
  rw [show cnPlusBoxInd L A volA (slotFibreState S e (slotPiece A S Φ) y)
      = ∑ i : Fin S.card, ∫ ζ in abox S.card L,
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Φ) y) ζ)^2 from rfl]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
  exact congrArg (·^2) (boxQInd_slotFibreState e volA A (slotPiece A S Φ) i ζ y).symm

end

end Work.SlotWord
