import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_sectorPieceProj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1.SectorPiece

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The four nested combinations of box projections at a sector piece

Each is the outer-slot application of `boxPInd_smul_slotIndep` (resp. `boxQInd_smul_slotIndep`)
with multiplier the sector indicator, whose slot-independence is
`Work.BoseFixB1.sectorSet_indicator_slotIndep`. -/

/-- The double condensate projection `P_a P_b` of a sector piece is the sector indicator times
`P_a P_b` of the state. -/
theorem boxPP_sectorPiece_apply {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
    (a b : Fin N) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A a
        (Work.UBBInputs8.boxPInd volA A b (Work.FockBridge.sectorPiece A k Φ)) x
      = (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.UBBInputs8.boxPInd volA A a (Work.UBBInputs8.boxPInd volA A b Φ) x := by
  rw [Work.BoseFixB1.boxPInd_sectorPiece volA hA b k Φ]
  exact congrFun (Work.BoseFixB1.boxPInd_smul_slotIndep volA hA a _
    (Work.BoseFixB1.sectorSet_indicator_slotIndep a k) (Work.UBBInputs8.boxPInd volA A b Φ)) x

/-- The mixed projection `P_a Q_b` of a sector piece is the sector indicator times `P_a Q_b` of
the state. -/
theorem boxPQ_sectorPiece_apply {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
    (a b : Fin N) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A a
        (Work.UBBInputs8.boxQInd volA A b (Work.FockBridge.sectorPiece A k Φ)) x
      = (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.UBBInputs8.boxPInd volA A a (Work.UBBInputs8.boxQInd volA A b Φ) x := by
  rw [Work.BoseFixB1.boxQInd_sectorPiece volA hA b k Φ]
  exact congrFun (Work.BoseFixB1.boxPInd_smul_slotIndep volA hA a _
    (Work.BoseFixB1.sectorSet_indicator_slotIndep a k) (Work.UBBInputs8.boxQInd volA A b Φ)) x

/-- The mixed projection `Q_a P_b` of a sector piece is the sector indicator times `Q_a P_b` of
the state. -/
theorem boxQP_sectorPiece_apply {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
    (a b : Fin N) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd volA A a
        (Work.UBBInputs8.boxPInd volA A b (Work.FockBridge.sectorPiece A k Φ)) x
      = (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.UBBInputs8.boxQInd volA A a (Work.UBBInputs8.boxPInd volA A b Φ) x := by
  rw [Work.BoseFixB1.boxPInd_sectorPiece volA hA b k Φ]
  exact congrFun (Work.BoseFixB1.boxQInd_smul_slotIndep volA hA a _
    (Work.BoseFixB1.sectorSet_indicator_slotIndep a k) (Work.UBBInputs8.boxPInd volA A b Φ)) x

/-- The double mean-free projection `Q_a Q_b` of a sector piece is the sector indicator times
`Q_a Q_b` of the state. -/
theorem boxQQ_sectorPiece_apply {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
    (a b : Fin N) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd volA A a
        (Work.UBBInputs8.boxQInd volA A b (Work.FockBridge.sectorPiece A k Φ)) x
      = (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.UBBInputs8.boxQInd volA A a (Work.UBBInputs8.boxQInd volA A b Φ) x := by
  rw [Work.BoseFixB1.boxQInd_sectorPiece volA hA b k Φ]
  exact congrFun (Work.BoseFixB1.boxQInd_smul_slotIndep volA hA a _
    (Work.BoseFixB1.sectorSet_indicator_slotIndep a k) (Work.UBBInputs8.boxQInd volA A b Φ)) x

/-! ## The target -/

theorem pairFrags_sectorPiece {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ} (i j : Fin N) (x : Submission.BoseGases.X N) :
    Work.BoseFixB1S.pairFrags volA A w w1 w2 om (Work.FockBridge.sectorPiece A k Φ) i j x
      = (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ i j x := by
  by_cases hx : x ∈ Work.FockBridge.sectorSet A k
  · -- in the sector the indicator is `1`, and each projection of the sector piece agrees with
    -- the projection of the state
    have hχ : (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    simp only [Work.BoseFixB1S.pairFrags, Work.BoseFixB1S.fg0, Work.BoseFixB1S.fg1,
      Work.BoseFixB1S.fg2a, Work.BoseFixB1S.fg2b, Work.BoseFixB1S.fg2c, Work.BoseFixB1S.fg3,
      Work.BoseFixB1S.fg4, Work.BoseFixB1S.boxQ4B]
    rw [boxPP_sectorPiece_apply volA hA k Φ i j x, boxPQ_sectorPiece_apply volA hA k Φ i j x,
      boxPP_sectorPiece_apply volA hA k Φ j i x, boxPQ_sectorPiece_apply volA hA k Φ j i x,
      boxQP_sectorPiece_apply volA hA k Φ j i x, boxQQ_sectorPiece_apply volA hA k Φ j i x,
      hχ]
    ring
  · -- outside the sector the indicator is `0`, so every fragment of the sector piece vanishes
    have hχ : (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x = 0 := by
      rw [Set.indicator_of_notMem hx]
    simp only [Work.BoseFixB1S.pairFrags, Work.BoseFixB1S.fg0, Work.BoseFixB1S.fg1,
      Work.BoseFixB1S.fg2a, Work.BoseFixB1S.fg2b, Work.BoseFixB1S.fg2c, Work.BoseFixB1S.fg3,
      Work.BoseFixB1S.fg4, Work.BoseFixB1S.boxQ4B]
    rw [boxPP_sectorPiece_apply volA hA k Φ i j x, boxPQ_sectorPiece_apply volA hA k Φ i j x,
      boxPP_sectorPiece_apply volA hA k Φ j i x, boxPQ_sectorPiece_apply volA hA k Φ j i x,
      boxQP_sectorPiece_apply volA hA k Φ j i x, boxQQ_sectorPiece_apply volA hA k Φ j i x,
      hχ]
    ring

end Work.BoseFixB1.SectorPiece
