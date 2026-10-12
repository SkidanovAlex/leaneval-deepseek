import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.flatPieceRTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open Submission.BoseGases

/-! ## Auxiliary pointwise forms of the three slot operators

`Pᵢ = indSlotᵢ · oneMeanᵢ`, `Qᵢ = indSlotᵢ · (id − oneMeanᵢ)`, `Rᵢ = (1 − indSlotᵢ) · id`.
These are the pointwise (applied) forms, which is what the induction below needs.  A factor that
is invariant under the slot-`i` update pulls out of the slot-`i` mean, so `cFold` over a list not
containing `i` pulls out. -/

theorem flatPieceAux_boxPInd_apply {N : ℕ} (V : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (i : Fin N) (f : X N → ℝ) (y : X N) :
    Work.UBBInputs8.boxPInd V A i f y = indSlot A i y * Work.BoseFixB1S.oneMean V A i f y := by
  simp only [Work.UBBInputs8.boxPInd, Work.BoseFixB1S.oneMean, indSlot, Work.BoseFixB1S.Aind]
  ring

theorem flatPieceAux_boxQInd_apply {N : ℕ} (V : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (i : Fin N) (f : X N → ℝ) (y : X N) :
    Work.UBBInputs8.boxQInd V A i f y
      = indSlot A i y * (f y - Work.BoseFixB1S.oneMean V A i f y) := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Work.BoseFixB1S.oneMean,
    indSlot, Work.BoseFixB1S.Aind]
  ring

theorem flatPieceAux_oneMean_mul_cFold {N : ℕ} (V : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (S T : Finset (Fin N)) (l : List (Fin N)) {i : Fin N} (hil : i ∉ l) (f : X N → ℝ)
    (y : X N) :
    Work.BoseFixB1S.oneMean V A i (fun z => cFold A S T l z * f z) y
      = cFold A S T l y * Work.BoseFixB1S.oneMean V A i f y := by
  have h := oneMean_mul_of_invariant (V := V) (A := A) i (h := cFold A S T l) (f := f)
    (fun y z => cFold_invariant A S T l hil y z)
  simpa using congrFun h y

/-- Every `(P,Q,R)`-flat piece factorises as the product of its slot factors `cOf` and its mean
fold `tFold`: `flatPieceRTList V A l S T Ψ = cFold A S T l · tFold V A S T l Ψ`. -/
theorem flatPieceRTList_factor {N : ℕ} (V : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (S T : Finset (Fin N)) (l : List (Fin N)) (hl : l.Nodup)
    (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1.flatPieceRTList V A l S T Ψ
      = fun y => Work.BoseFixB1.cFold A S T l y * Work.BoseFixB1.tFold V A S T l Ψ y := by
  revert hl
  induction l with
  | nil =>
    intro _
    funext y
    simp
  | cons i l ih =>
    intro hl
    obtain ⟨hil, hl'⟩ := List.nodup_cons.mp hl
    rw [flatPieceRTList_cons, ih hl']
    by_cases hiS : i ∈ S
    · rw [if_pos hiS, tFold_cons_of_mem_S V A S T hiS l Ψ]
      funext y
      rw [cFold_cons_apply, cOf_of_mem (Finset.mem_union_left T hiS),
        flatPieceAux_boxPInd_apply,
        flatPieceAux_oneMean_mul_cFold V A S T l hil (tFold V A S T l Ψ) y]
      ring
    · by_cases hiT : i ∈ T
      · rw [if_neg hiS, if_pos hiT, tFold_cons_of_mem_T V A S T hiS hiT l Ψ]
        funext y
        rw [Pi.sub_apply, cFold_cons_apply, cOf_of_mem (Finset.mem_union_right S hiT),
          flatPieceAux_boxQInd_apply,
          flatPieceAux_oneMean_mul_cFold V A S T l hil (tFold V A S T l Ψ) y]
        ring
      · rw [if_neg hiS, if_neg hiT, tFold_cons_of_notMem V A S T hiS hiT l Ψ]
        funext y
        rw [cFold_cons_apply, cOf_of_notMem (by simp [hiS, hiT]), rInd_apply]
        ring

end Work.BoseFixB1
