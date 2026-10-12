import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.PerSector.Support
import Submission.Work.PerSector.boxQInd_slotPiece_eq_of_mem_slotSet
import Submission.Work.PerSector.boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PerSector

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

variable {N : ℕ}

/-- **The pointwise slot decomposition of the projected square amplitude.**  FS's projection
`Q_{A,i}` of the state has squared modulus equal to the sum of the squared moduli of its projections
of the *slot pieces*: at a configuration `x` at most one slot piece has a nonzero projection (the
one whose slot set is the occupant of `x`), the projections are supported in the disjoint shift sets
`slotShiftSet A S i` (`boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet`), and on its own slot set
the projection of the piece coincides with the projection of the state
(`boxQInd_slotPiece_eq_of_mem_slotSet`).  This is the atom of the slot additivity of the box excited
count `n₊(B)`. -/
theorem sq_boxQInd_eq_sum_sq_boxQInd_slotPiece {A : Set ℝ³} (hA : MeasurableSet A) {volA : ℝ}
    (i : Fin N) {Φ : X N → ℝ} (x : X N) :
    (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∑ S : Finset (Fin N),
          (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x) ^ 2 := by
  classical
  -- The occupant of `x`: the slot set whose particles are exactly those of `x` lying in `A`.
  obtain ⟨S₀, hxS₀⟩ : ∃ S : Finset (Fin N), x ∈ slotSet A S := by
    refine ⟨Finset.univ.filter (fun j : Fin N => x j ∈ A), ?_⟩
    rw [mem_slotSet_iff]
    intro j
    simp
  -- Only the summand at the occupant survives.
  rw [Finset.sum_eq_single_of_mem S₀ (Finset.mem_univ S₀) ?_]
  · -- At the occupant, the projection of the piece is the projection of the state.
    exact congrArg (· ^ 2) (boxQInd_slotPiece_eq_of_mem_slotSet hA i hxS₀)
  · -- At every other slot set, the shift set misses `x`, so the projection of the piece vanishes.
    intro S _ hS
    have hxnot : x ∉ slotShiftSet A S i := by
      intro hxsh
      -- A configuration in the shift set lies in the slot set of `S`, hence `S` is the occupant.
      have hxS : x ∈ slotSet A S := by
        rw [mem_slotSet_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          exact ⟨fun _ => hxsh.1, fun _ => hxsh.2.1⟩
        · exact hxsh.2.2 j hj
      exact hS (slotSet_eq_of_mem hxS hxS₀)
    rw [boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet hA i S hxnot]
    ring

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **The pointwise slot decomposition of the projected square amplitude**, re-exported at the
chapter's outer namespace `Work.PerSector` (the declaration proved above sits in the doubly nested
namespace produced by this file's header). -/
theorem sq_boxQInd_eq_sum_sq_boxQInd_slotPiece
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) {volA : ℝ}
    (i : Fin N) {Φ : X N → ℝ} (x : X N) :
    (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
      = ∑ S : Finset (Fin N),
          (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x) ^ 2 :=
  Work.PerSector.Work.PerSector.sq_boxQInd_eq_sum_sq_boxQInd_slotPiece hA i x

end Work.PerSector
