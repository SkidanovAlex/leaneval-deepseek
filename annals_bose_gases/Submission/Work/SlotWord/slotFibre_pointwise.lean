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
# `Work.SlotWord.slotFibre_pointwise`

The pointwise atoms of the fibre factorisation of the spectral `p`-diagonal form: the fibre
embedding `fibreIn`, the commutation of the box mean-free projection `Q_B` with it, and the
resulting pointwise identity for the windowed amplitude `tBamp`.
-/

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The fibre embedding -/

/-- The fibre embedding. -/
def fibreIn (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (y : SlotOut N S → ℝ³) :
    X S.card → X N :=
  fun z => slotComb S (fun i' => z (e i')) y

theorem slotFibreState_eq_comp (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (Ψ : X N → ℝ) (y : SlotOut N S → ℝ³) :
    slotFibreState S e Ψ y = fun z => Ψ (fibreIn S e y z) := rfl

@[simp] theorem fibreIn_apply (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (y : SlotOut N S → ℝ³) (z : X S.card) (i : SlotIn N S) :
    fibreIn S e y z i.1 = z (e i) := by
  rw [fibreIn, slotComb_apply, dif_pos i.2]

theorem fibreIn_apply_self (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (i : Fin N) (hi : i ∈ S) (y : SlotOut N S → ℝ³) (z : X S.card) :
    fibreIn S e y z i = z (e ⟨i, hi⟩) :=
  fibreIn_apply S e y z ⟨i, hi⟩

/-- Updating the slot `i.1` of the reassembly is updating the fibre slot `i`. -/
theorem slotComb_update (S : Finset (Fin N)) (y : SlotOut N S → ℝ³)
    (zc : SlotIn N S → ℝ³) (i : SlotIn N S) (u : ℝ³) :
    slotComb S (Function.update zc i u) y = Function.update (slotComb S zc y) i.1 u := by
  funext i'
  by_cases h1 : i' ∈ S
  · rw [slotComb_apply, dif_pos h1]
    rw [Function.update_apply (slotComb S zc y) i.1 u i']
    rw [slotComb_apply, dif_pos h1]
    rw [Function.update_apply zc i u (⟨i', h1⟩ : SlotIn N S)]
    by_cases h2 : (⟨i', h1⟩ : SlotIn N S) = i
    · rw [if_pos h2, if_pos (Subtype.ext_iff.mp h2)]
    · rw [if_neg h2, if_neg (fun hc : i' = ↑i => h2 (Subtype.ext hc))]
  · rw [slotComb_apply, dif_neg h1]
    rw [Function.update_apply (slotComb S zc y) i.1 u i',
        if_neg (fun hc : i' = ↑i => h1 (hc.symm ▸ i.2))]
    rw [slotComb_apply, dif_neg h1]

theorem fibreIn_update (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (i : Fin N) (hi : i ∈ S) (y : SlotOut N S → ℝ³) (z : X S.card) (u : ℝ³) :
    Function.update (fibreIn S e y z) i u
      = fibreIn S e y (Function.update z (e ⟨i, hi⟩) u) := by
  have hc : (fun i'' : SlotIn N S => Function.update z (e ⟨i, hi⟩) u (e i''))
      = Function.update (fun i'' : SlotIn N S => z (e i'')) ⟨i, hi⟩ u := by
    funext i''
    rw [Function.update_apply, Function.update_apply]
    by_cases h : i'' = ⟨i, hi⟩
    · rw [if_pos (congrArg e h), if_pos h]
    · rw [if_neg (fun hc => h (e.injective hc)), if_neg h]
  rw [fibreIn, fibreIn, hc, slotComb_update]

/-! ## 2. The box projection transfers along the fibre embedding -/

theorem boxQInd_slotFibre_transfer (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    (i : Fin N) (hi : i ∈ S) (y : SlotOut N S → ℝ³) (Ψ : X N → ℝ) (volA : ℝ) (A : Set ℝ³)
    (z : X S.card) :
    boxQInd volA A (e ⟨i, hi⟩) (slotFibreState S e Ψ y) z
      = boxQInd volA A i Ψ (fibreIn S e y z) := by
  have h1 : fibreIn S e y z i = z (e ⟨i, hi⟩) := fibreIn_apply_self S e i hi y z
  have hInt : (∫ u in A, Ψ (slotComb S (fun i' => Function.update z (e ⟨i, hi⟩) u (e i')) y))
      = ∫ u in A, Ψ (Function.update (fibreIn S e y z) i u) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show Ψ (slotComb S (fun i' => Function.update z (e ⟨i, hi⟩) u (e i')) y)
      = Ψ (Function.update (fibreIn S e y z) i u)
    rw [fibreIn_update S e i hi y z u, fibreIn]
  simp only [boxQInd, boxPInd, slotFibreState, slotFibre]
  rw [h1, hInt]
  simp only [fibreIn]

/-! ## 3. The pointwise amplitude identity -/

theorem tBamp_boxQInd_slotPiece_eq_fibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card)
    (i : Fin N) (hi : i ∈ S) (p : ℝ³) (z : X S.card) (y : SlotOut N S → ℝ³) :
    Work.SmallBoxTBWord.tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i
        (fibreIn S e y z)
      = Work.SmallBoxTBWord.tBamp (chiB L d u) p
          (boxQInd (boxMass L d u) (dlBox L d u) (e ⟨i, hi⟩)
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) (e ⟨i, hi⟩) z := by
  rw [Work.SmallBoxTBWord.tBamp, Work.SmallBoxTBWord.tBamp]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  refine congrArg (fun t : ℝ =>
    (chiB L d u w : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) * (t : ℂ)) ?_
  rw [fibreIn_update S e i hi y z w]
  exact (boxQInd_slotFibre_transfer S e i hi y (slotPiece (dlBox L d u) S Φ)
    (boxMass L d u) (dlBox L d u) (Function.update z (e ⟨i, hi⟩) w)).symm

end

end Work.SlotWord
