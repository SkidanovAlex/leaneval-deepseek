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

/-- **The box projection `Q_{B,i}` of a slot piece is supported in the projection shift set.**  FS's
box mean-free projection in slot `i` (`Work.UBBInputs8.boxQInd volA A i`, whose second term is the
mean over `A` of the slot-`i` fibre) replaces slot `i` by a point of `A`; applied to the slot piece
`slotPiece A S Φ`, both its terms are killed unless slot `i` lies in `A` and all the *other* slots
agree with `S` — i.e. unless the configuration lies in `slotShiftSet A S i`.  (If `i ∉ S` the
projection vanishes identically, which the shift set also records since it requires `i ∈ S`.)  This
is the atom of the slot additivity of the localised kinetic word: the projections of the different
slot pieces have disjointly supported supports. -/
theorem boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet {A : Set ℝ³} (hA : MeasurableSet A)
    {volA : ℝ} (i : Fin N) {Φ : X N → ℝ} (S : Finset (Fin N)) {x : X N}
    (hx : x ∉ slotShiftSet A S i) :
    Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x = 0 := by
  classical
  -- **The combinatorial core.**  If slot `i` of `x` lies in `A`, then no configuration agreeing
  -- with `x` off `i` and carrying a point of `A` at slot `i` can lie in the slot set `S`: either
  -- `i ∈ S`, in which case `x` itself would already lie in the shift set (its remaining slots
  -- agreeing with `S`), or `i ∉ S`, in which case slot `i` alone (a point of `A` while `i ∉ S`)
  -- contradicts the slot condition.
  have hkey : x i ∈ A → ∀ y : X N, y i ∈ A → (∀ j : Fin N, j ≠ i → y j = x j) →
      y ∉ slotSet A S := by
    intro hxi y hyi hagree hmem
    have hmemall : ∀ j : Fin N, (y j ∈ A ↔ j ∈ S) := (mem_slotSet_iff A S y).mp hmem
    by_cases hiS : i ∈ S
    · refine hx ⟨hiS, hxi, fun j hj => ?_⟩
      rw [← hagree j hj]
      exact hmemall j
    · exact hiS ((hmemall i).mp hyi)
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ A
  · -- slot `i` of `x` is in `A`: both terms die, the first because `x ∉ slotSet A S`, the second
    -- because the fibre integral only samples configurations with a point of `A` in slot `i`.
    have hxnot : x ∉ slotSet A S := hkey hxi x hxi (fun j _ => rfl)
    have hupd : ∀ z ∈ A, Function.update x i z ∉ slotSet A S :=
      fun z hz => hkey hxi _ (by rw [Function.update_self]; exact hz)
        (fun j hj => Function.update_of_ne hj z x)
    have hxzero : slotPiece A S Φ x = 0 := Set.indicator_of_notMem hxnot Φ
    have hzero : A.indicator (fun z => slotPiece A S Φ (Function.update x i z))
        = (fun _ => (0 : ℝ)) := by
      funext z
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz]
        exact Set.indicator_of_notMem (hupd z hz) Φ
      · rw [Set.indicator_of_notMem hz]
    have hInt : (∫ z in A, slotPiece A S Φ (Function.update x i z)) = 0 := by
      rw [← integral_indicator hA, hzero]
      simp
    rw [Set.indicator_of_mem hxi, hxzero, hInt]
    ring
  · -- slot `i` of `x` is outside `A`: both terms carry the box indicator at `x i`.
    rw [Set.indicator_of_notMem hxi]
    ring

end Work.PerSector

open Submission BoseGases

variable {N : ℕ}

/-- **The box projection `Q_{B,i}` of a slot piece is supported in the projection shift set**,
re-exported at the chapter's outer namespace `Work.PerSector` (the declaration proved above sits in
the doubly nested namespace produced by this file's header). -/
theorem boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {volA : ℝ} (i : Fin N) {Φ : X N → ℝ} (S : Finset (Fin N)) {x : X N}
    (hx : x ∉ slotShiftSet A S i) :
    Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ) x = 0 :=
  Work.PerSector.Work.PerSector.boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet hA i S hx

end Work.PerSector
