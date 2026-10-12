import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PerSector.Strat
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

/-- **On its own slot set the projection sees the state.**  If `x` lies in the slot set of `S`, then
FS's box projection `Q_{B,i}` applied to the state and to the slot piece at `S` agree at `x`: the
box-indicator terms agree because the piece equals the state at `x`, and the fibre averages agree
because on the whole fibre `z ∈ A ↦ x[i↦z]` stays in the slot set (when `x i ∈ A`), while if
`x i ∉ A` both sides are killed by the box indicator. -/
theorem boxQInd_slotPiece_eq_of_mem_slotSet {A : Set ℝ³} (hA : MeasurableSet A) {volA : ℝ}
    (i : Fin N) {Φ : X N → ℝ} {S : Finset (Fin N)} {x : X N} (hx : x ∈ slotSet A S) :
    Work.UBBInputs8.boxQInd volA A i Φ x
      = Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x := by
  classical
  -- The slot condition: slot `j` of `x` lies in `A` exactly when `j ∈ S`.
  have hxall : ∀ j : Fin N, (x j ∈ A ↔ j ∈ S) := (mem_slotSet_iff A S x).mp hx
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ A
  · -- Slot `i` of `x` is in the box: the box indicator is `1`, the state and its slot piece
    -- already agree at `x`, and they also agree along the whole slot-`i` fibre over `A`.
    have hiS : i ∈ S := (hxall i).mp hxi
    have hxmem : slotPiece A S Φ x = Φ x := Set.indicator_of_mem hx Φ
    have hind : A.indicator (fun _ => (1 : ℝ)) (x i) = 1 := by
      rw [Set.indicator_of_mem hxi]
    -- Replacing slot `i` of `x` by a point of `A` keeps the configuration in the slot set.
    have hupd : ∀ z ∈ A, Function.update x i z ∈ slotSet A S := by
      intro z hz j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        exact ⟨fun _ => hiS, fun _ => hz⟩
      · rw [Function.update_of_ne hj z x]
        exact hxall j
    have hInt : (∫ z in A, Φ (Function.update x i z))
        = ∫ z in A, slotPiece A S Φ (Function.update x i z) :=
      setIntegral_congr_fun hA (fun z hz => (Set.indicator_of_mem (hupd z hz) Φ).symm)
    rw [hInt, hind, hxmem]
  · -- Slot `i` of `x` is outside the box: both terms carry the box indicator `0`.
    have hind : A.indicator (fun _ => (1 : ℝ)) (x i) = 0 := by
      rw [Set.indicator_of_notMem hxi]
    rw [hind]
    ring

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **On its own slot set the projection sees the state**, re-exported at the chapter's outer
namespace `Work.PerSector` (the declaration proved above sits in the doubly nested namespace
produced by this file's header). -/
theorem boxQInd_slotPiece_eq_of_mem_slotSet
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) {volA : ℝ}
    (i : Fin N) {Φ : X N → ℝ} {S : Finset (Fin N)} {x : X N} (hx : x ∈ slotSet A S) :
    Work.UBBInputs8.boxQInd volA A i Φ x
      = Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x :=
  Work.PerSector.Work.PerSector.boxQInd_slotPiece_eq_of_mem_slotSet hA i hx

end Work.PerSector
