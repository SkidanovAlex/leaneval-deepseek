import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.PerSector.Support
import Submission.Work.PerSector.boxQInd_slotPiece_eq_of_mem_slotSet
import Submission.Work.PerSector.tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PerSector.sum_tBamp_normSq_slotPiece` — the amplitude Parseval atom

The squared modulus of the windowed amplitude of a state is the sum of the squared moduli of the
amplitudes of its *slot pieces*:

    ‖tBamp χ p (Q_{A,i}Φ) i x‖² = Σ_{S : Finset (Fin N)} ‖tBamp χ p (Q_{A,i}(slotPiece A S Φ)) i x‖² .

**The measurability hypothesis.**  The proof needs the congruence of the two slot-`i` fibre averages
`∫_{z ∈ A} Φ(x[i↦z])` and `∫_{z ∈ A} (1_{slotSet A S}Φ)(x[i↦z])`, whose integrands agree *pointwise
on `A`*; Mathlib's set-integral congruence `MeasureTheory.setIntegral_congr_fun` carries the
hypothesis `MeasurableSet A`, and every sibling atom in this directory
(`boxQInd_slotPiece_eq_of_mem_slotSet`, `boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet`,
`sq_boxQInd_eq_sum_sq_boxQInd_slotPiece`) carries it as well — so it is carried here too.  (An
attempt at the `hA`-free statement was reported unprovable in Mathlib by a colleague.)

Contents:

* `tBamp_slotPiece_eq_of_mem_slotAmpSet` — on its own amplitude shift set the amplitude of a slot
  piece is the amplitude of the state (the fibre congruence for `tBamp`);
* **`sum_tBamp_normSq_slotPiece`** — the Parseval decomposition: at each `x` at most one summand is
  nonzero and it equals the left-hand side.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- **On its own amplitude shift set the amplitude of a slot piece is the amplitude of the state.**
If `x ∈ slotAmpSet A S i` then every fibre point `x[i↦z]` with `z ∈ A` lies in the slot set of `S`
(that is exactly what the shift-set condition says off slot `i`, and slot `i` is moved into `A`),
so the two projections agree along the fibre and `tBamp` — an integral along that fibre — cannot
distinguish the state from its slot piece. -/
theorem tBamp_slotPiece_eq_of_mem_slotAmpSet {A : Set ℝ³} (hA : MeasurableSet A) (χ : ℝ³ → ℝ)
    (hχ : ∀ z, χ z ≠ 0 → z ∈ A) {volA : ℝ} (i : Fin N) {Φ : X N → ℝ}
    (S : Finset (Fin N)) (p : ℝ³) {x : X N} (hx : x ∈ slotAmpSet A S i) :
    Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ)) i x
      = Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x := by
  classical
  refine Work.FockBridge.tBamp_congr_of_eqOn_fibre χ hχ p i (fun z hz => ?_)
  have hy : Function.update x i z ∈ slotSet A S := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact ⟨fun _ => hx.1, fun _ => hz⟩
    · rw [Function.update_of_ne hj z x]
      exact hx.2 j hj
  exact (boxQInd_slotPiece_eq_of_mem_slotSet hA i hy).symm

/-- **The squared-norm (Parseval) slot decomposition of the windowed amplitude.**  At every
configuration `x` there is exactly one slot index `S₀` with `x ∈ slotAmpSet A S₀ i` — the slot set
`{i} ∪ {j ≠ i | x j ∈ A}` of the fibre configuration `x[i↦z]`, `z ∈ A`.  On that shift set the
amplitude of the piece equals the amplitude of the state
(`tBamp_slotPiece_eq_of_mem_slotAmpSet`), while for every `S ≠ S₀` the amplitude of the piece
vanishes by disjointness of the amplitude shift sets
(`tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet`, `slotAmpSet_disjoint`).  Hence at each `x` at most
one summand on the right is nonzero and it equals the left-hand side. -/
theorem sum_tBamp_normSq_slotPiece {A : Set ℝ³} (hA : MeasurableSet A) (χ : ℝ³ → ℝ)
    (hχ : ∀ z : ℝ³, χ z ≠ 0 → z ∈ A) {volA : ℝ} (i : Fin N) {Φ : X N → ℝ} (p : ℝ³) (x : X N) :
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
      = ∑ S : Finset (Fin N),
          ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ)) i x‖ ^ 2 := by
  classical
  -- the slot index of the fibre configuration: slot `i` together with the other slots of `x` in `A`
  set S0 : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => j = i ∨ x j ∈ A) with hS0
  have hi0 : i ∈ S0 := by
    rw [hS0]; simp
  have hx0 : x ∈ slotAmpSet A S0 i := by
    refine ⟨hi0, fun j hj => ?_⟩
    rw [hS0, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun hji => absurd hji hj) (fun h => h)⟩
  -- the piece at `S₀` reproduces the full amplitude
  have hB : Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (slotPiece A S0 Φ)) i x :=
    (tBamp_slotPiece_eq_of_mem_slotAmpSet hA χ hχ i S0 p hx0).symm
  -- every other piece has vanishing amplitude at `x`
  have hzero : ∀ S : Finset (Fin N), S ≠ S0 →
      ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (slotPiece A S Φ)) i x‖ ^ 2 = 0 := by
    intro S hne
    have hxnot : x ∉ slotAmpSet A S i := fun hxS =>
      Set.disjoint_left.mp (slotAmpSet_disjoint hne) hxS hx0
    rw [tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet χ hχ i S p hxnot]
    simp
  rw [hB]
  exact (Finset.sum_eq_single S0 (fun S _ hne => hzero S hne)
    (fun hnot => absurd (Finset.mem_univ S0) hnot)).symm

end Work.PerSector
