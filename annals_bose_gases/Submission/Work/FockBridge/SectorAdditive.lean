import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.SectorAdditive` — the capstone of the sector decomposition

The corpus per-box kinetic word `tBwordInd a A volA χ s ε c` (FS `eq:DefT`/`eq:appTB` at the box
`A`: the gap term `tbGapCoeff s ε·n₊(B)` plus the spectral term
`Q_Bχ_B[√−Δ−c]₊²χ_BQ_B`) is **sector-additive**: it is the sum of its values on the state's
`A`-occupancy sector pieces.  Given the per-slot additivity of the excited count
(`cnPlusBoxInd_eq_sum_sectorPiece`) and of the `p`-diagonal form
(`tBdiagSlotInd_eq_sum_sectorPiece`), the only content is the rearrangement of the doubly indexed
sum — i.e. *no analysis at all*.  This is the formal locality statement that the named residual
`Work.FockBridge.FockSectorBridge` leaves to the count-indexed delivered bound. -/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.UBBInputs8
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-box kinetic word is sector-additive**: the gap term and the spectral term both
decompose over the `A`-occupancy sector pieces of the state. -/
theorem tBwordInd_eq_sum_sectorPiece {N : ℕ} {A : Set ℝ³} {volA a s ε c : ℝ} {χ : ℝ³ → ℝ}
    {Φ : X N → ℝ}
    (hcn : ∀ i : Fin N, (∫ x in abox N a, (boxQInd volA A i Φ x) ^ 2)
      = ∑ k ∈ Finset.range (N + 1),
          ∫ x in abox N a, (boxQInd volA A i (sectorPiece A k Φ) x) ^ 2)
    (hd : ∀ i : Fin N, (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖
          * ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ k ∈ Finset.range (N + 1),
          ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖
            * ((a ^ 3)⁻¹ * ∫ x in abox N a,
              ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2)) :
    Work.UBBInputs8.tBwordInd a A volA χ s ε c Φ
      = ∑ k ∈ Finset.range (N + 1),
          Work.UBBInputs8.tBwordInd a A volA χ s ε c (sectorPiece A k Φ) := by
  have hcn' : (∑ i : Fin N, ∫ x in abox N a, (boxQInd volA A i Φ x) ^ 2)
      = ∑ k ∈ Finset.range (N + 1),
          ∑ i : Fin N, ∫ x in abox N a,
            (boxQInd volA A i (sectorPiece A k Φ) x) ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hcn i), Finset.sum_comm]
  have hd' : (∑ i : Fin N, ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖
        * ((a ^ 3)⁻¹ * ∫ x in abox N a,
          ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i Φ) i x‖ ^ 2))
      = ∑ k ∈ Finset.range (N + 1),
          ∑ i : Fin N, ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖
            * ((a ^ 3)⁻¹ * ∫ x in abox N a,
              ‖SmallBoxTBWord.tBamp χ p (boxQInd volA A i (sectorPiece A k Φ)) i x‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hd i), Finset.sum_comm]
  simp only [Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.cnPlusBoxInd, hcn',
    Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, hd']

end Work.FockBridge
