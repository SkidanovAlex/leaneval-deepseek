import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.fix_zero_is_euclidean
import Submission.Work.Mostow.finite_nearStab

/-!
# Setup for `rotData3`: the rotation/axis chapter for `n = 3`

Elementary facts about the effective matrix `emat g` and the orientation character.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Work.Mostow
open Matrix

noncomputable section

/-! ## Part 1: `emat` is a homomorphism -/

theorem emat_mul {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (g h : LeanEval.Geometry.MostowRigidity.PO n 1) : emat (g * h) = emat g * emat h := by
  apply Matrix.ext_of_hlift
  intro u
  rw [← Matrix.mulVec_mulVec]
  simp only [emat_hlift]
  exact congrArg hlift ((POBasic.ofProp hA).mul_smul g h u)

theorem emat_one {n : ℕ} (hA : Submission.Mostow.POActionProp n) :
    emat (1 : LeanEval.Geometry.MostowRigidity.PO n 1) = 1 := by
  apply Matrix.ext_of_hlift
  intro u
  rw [Matrix.one_mulVec, emat_hlift, (POBasic.ofProp hA).one_smul]

theorem emat_pow {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (k : ℕ) : emat (g ^ k) = (emat g) ^ k := by
  induction k with
  | zero => simpa using emat_one (n := n) hA
  | succ k ih => rw [pow_succ, pow_succ, emat_mul hA, ih]

theorem emat_pow_eq_one {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    {g : LeanEval.Geometry.MostowRigidity.PO n 1} {k : ℕ} (hk : g ^ k = 1) :
    (emat g) ^ k = 1 := by
  rw [← emat_pow hA, hk, emat_one (n := n) hA]

theorem emat_injective {n : ℕ} (hA : Submission.Mostow.POActionProp n) :
    Function.Injective (emat (n := n)) := by
  intro g h hgh
  have h1 : ∀ u : Submission.Mostow.E n, g • u = h • u := by
    intro u
    have h2 := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ =>
      Matrix.mulVec M (hlift u)) hgh
    rw [emat_hlift, emat_hlift] at h2
    exact Submission.Mostow.Hyper.hlift_injective h2
  have h2 : ∀ u : Submission.Mostow.E n, (h⁻¹ * g) • u = u := by
    intro u
    rw [(POBasic.ofProp hA).mul_smul, h1 u, ← (POBasic.ofProp hA).mul_smul, inv_mul_cancel,
      (POBasic.ofProp hA).one_smul]
  have h3 : h⁻¹ * g = 1 := (POBasic.ofProp hA).faithful _ h2
  calc g = h * (h⁻¹ * g) := by group
    _ = h * 1 := by rw [h3]
    _ = h := mul_one h

/-! ## Part 2: the orientation character -/

theorem det_emat3 (g : LeanEval.Geometry.MostowRigidity.PO 3 1) :
    (emat g).det = (Submission.Mostow.mat (Submission.Mostow.rep g)).det := by
  have h4 : (Submission.Mostow.tsign (Submission.Mostow.rep g)) ^ 4 = 1 := by
    have h2 : (Submission.Mostow.tsign (Submission.Mostow.rep g)) ^ 2 = 1 := by
      rw [sq]; exact Submission.Mostow.Hyper.tsign_mul_self _
    calc (Submission.Mostow.tsign (Submission.Mostow.rep g)) ^ 4
        = ((Submission.Mostow.tsign (Submission.Mostow.rep g)) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h2]; ring
  rw [emat, Matrix.det_smul]
  have hc : Fintype.card (Fin 3 ⊕ Fin 1) = 4 := by simp
  rw [hc, h4, one_mul]

theorem isOriented_iff_det (g : LeanEval.Geometry.MostowRigidity.PO 3 1) :
    IsOriented g ↔ 0 < (emat g).det := by
  rw [IsOriented, det_emat3]

theorem isOriented_one (hA : Submission.Mostow.POActionProp 3) :
    IsOriented (1 : LeanEval.Geometry.MostowRigidity.PO 3 1) := by
  rw [isOriented_iff_det, emat_one hA, Matrix.det_one]
  norm_num

/-- The orientation-preserving subgroup of `PO 3 1`. -/
def orientSub (hA : Submission.Mostow.POActionProp 3) :
    Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1) where
  carrier := {g | IsOriented g}
  mul_mem' := by
    intro g h hg hh
    have hg' : IsOriented g := hg
    have hh' : IsOriented h := hh
    show IsOriented (g * h)
    rw [isOriented_iff_det] at hg' hh' ⊢
    rw [emat_mul hA, Matrix.det_mul]
    exact mul_pos hg' hh'
  one_mem' := isOriented_one hA
  inv_mem' := by
    intro g hg
    have hg' : IsOriented g := hg
    show IsOriented g⁻¹
    rw [isOriented_iff_det] at hg' ⊢
    have h2 : (emat g) * (emat g⁻¹) = 1 := by
      rw [← emat_mul hA, mul_inv_cancel, emat_one hA]
    have h3 : (emat g).det * (emat g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, h2, Matrix.det_one]
    nlinarith [h3, hg']

end

end Work.Mostow.gapA
