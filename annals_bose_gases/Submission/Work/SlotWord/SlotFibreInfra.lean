import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.SlotFibreInfra` — the algebraic core of the fibre factorisation
of the excited count `cnPlusBoxInd`

The two purely algebraic (no analysis) facts on which the fibre factorisation of the box excited
count rests:

* `upd_slotComb` — **the slot-`i` fibre of the reassembled configuration is the reassembly of the
  updated in-box configuration**: replacing the particle at slot `(e.symm i).1` of
  `slotComb S (ζ ∘ e) y` by `z` is the same as replacing the in-box coordinate `i` of `ζ` by `z`
  (and keeping the outside configuration `y`).  This is the compatibility of `Function.update`
  with the slot splitting along a bijection `e : SlotIn N S ≃ Fin S.card`.

* `boxQInd_slotFibreState` — **FS's box projection `Q_{B,i}` commutes with the transport of a
  state to its fibre**: the projection of the transported fibre `slotFibreState S e Ψ y` at slot
  `i : Fin S.card` equals the projection of `Ψ` at the slot `(e.symm i).1 : Fin N` of the
  reassembled configuration.  Since `Q_{B,i}` is an algebraic expression in `Ψ ζ` and the
  fibre mean `∫_{w ∈ A} Ψ (ζ_{i←w})`, this is exactly `upd_slotComb` plus the trivial identity
  `slotComb S (ζ ∘ e) y (e.symm i).1 = ζ i`.

Both are needed to compare the `N`-particle excited count of a slot piece with the
`S.card`-particle excited count of its fibre (`cnPlusBoxInd_slotFibre`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- **The slot-`i` fibre of the reassembly is the reassembly of the updated in-box
configuration.**  For a bijection `e : SlotIn N S ≃ Fin S.card`, an in-box configuration `ζ`, an
outside configuration `y`, a slot `i : Fin S.card` and `z : ℝ³`,

    (slotComb S (ζ ∘ e) y)[(e.symm i) ← z] = slotComb S ((ζ[i ← z]) ∘ e) y .

This is the compatibility of `Function.update` with the slot splitting: replacing the particle in
slot `e.symm i` (an in-box slot, so the value at that slot is `ζ (e (e.symm i)) = ζ i`) by `z` is
the same as replacing the `i`-th in-box coordinate by `z`. -/
lemma upd_slotComb {S : Finset (Fin N)} (e : SlotIn N S ≃ Fin S.card)
    (ζ : X S.card) (i : Fin S.card) (z : ℝ³)
    (y : SlotOut N S → ℝ³) :
    slotComb S (fun k : SlotIn N S => (Function.update ζ i z) (e k)) y
      = Function.update (slotComb S (fun k : SlotIn N S => ζ (e k)) y) (e.symm i).1 z := by
  funext j
  simp only [slotComb_apply, Function.update_apply]
  by_cases hj : j = (e.symm i).1
  · have hjS : j ∈ S := by rw [hj]; exact (e.symm i).2
    rw [if_pos hj, dif_pos hjS]
    have hk : (⟨j, hjS⟩ : SlotIn N S) = e.symm i := Subtype.ext hj
    have hek : e ⟨j, hjS⟩ = i := by rw [hk]; exact e.apply_symm_apply i
    rw [if_pos hek]
  · rw [if_neg hj]
    by_cases hjS : j ∈ S
    · rw [dif_pos hjS, dif_pos hjS]
      have hene : ¬ (e ⟨j, hjS⟩ = i) := by
        intro h
        exact hj (Subtype.ext_iff.mp ((Equiv.eq_symm_apply e).mpr h))
      rw [if_neg hene]
    · rw [dif_neg hjS, dif_neg hjS]

/-- **FS's box projection commutes with the transport to the fibre.**  For any state
`Ψ : X N → ℝ`, any bijection `e : SlotIn N S ≃ Fin S.card`, and any `ζ : X S.card`, `y`,

    Q_{A,i}(slotFibreState S e Ψ y)(ζ)
      = Q_{A,(e.symm i).1}(Ψ)(slotComb S (ζ ∘ e) y) .

Both sides are the same algebraic expression: the box indicator is evaluated at
`ζ i = (slotComb S (ζ ∘ e) y) (e.symm i).1`, the first term is `Ψ` at the two reassemblies (equal
by `slotFibreState_apply`), and the fibre mean matches by `upd_slotComb`. -/
lemma boxQInd_slotFibreState {S : Finset (Fin N)} (e : SlotIn N S ≃ Fin S.card)
    (volA : ℝ) (A : Set ℝ³) (Ψ : X N → ℝ) (i : Fin S.card) (ζ : X S.card)
    (y : SlotOut N S → ℝ³) :
    boxQInd volA A i (slotFibreState S e Ψ y) ζ
      = boxQInd volA A (e.symm i).1 Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y) := by
  classical
  have h1 : (slotComb S (fun k : SlotIn N S => ζ (e k)) y) (e.symm i).1 = ζ i := by
    rw [slotComb_apply, dif_pos (e.symm i).2]
    exact congrArg ζ (e.apply_symm_apply i)
  have h2 : slotFibreState S e Ψ y ζ
      = Ψ (slotComb S (fun k : SlotIn N S => ζ (e k)) y) :=
    slotFibreState_apply S e Ψ y ζ
  have h3 : (∫ z in A, slotFibreState S e Ψ y (Function.update ζ i z))
      = ∫ z in A, Ψ (Function.update
          (slotComb S (fun k : SlotIn N S => ζ (e k)) y) (e.symm i).1 z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [slotFibreState_apply, upd_slotComb]
  rw [boxQInd, boxPInd, boxQInd, boxPInd, h1, ← h2, h3]

/-- **The projection shift set sits inside the slot set.**  A configuration in which slot `i` lies in
`B` and all *other* slots agree with `S` (and `i ∈ S`) lies in the slot set of `S`: slot `i` is then
automatically all right, and the other slots agree by hypothesis. -/
lemma slotShiftSet_subset_slotSet {A : Set ℝ³} (S : Finset (Fin N)) (i : Fin N) :
    slotShiftSet A S i ⊆ slotSet A S := by
  intro x hx
  rw [mem_slotSet_iff]
  intro k
  by_cases hk : k = i
  · subst hk
    exact ⟨fun _ => hx.1, fun _ => hx.2.1⟩
  · exact hx.2.2 k hk

end Work.SlotWord
