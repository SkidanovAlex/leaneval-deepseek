import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.centralizer_aux

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-! ## Conjugating a matrix, and the element inverting the traceless part -/

lemma adjugate_eq_inv_of_det_eq_one' {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M.det = 1) : M.adjugate = M⁻¹ := by
  rw [Matrix.inv_def, hM]
  simp

lemma conj_smul' {F : Type*} [Field F] (M A : Matrix (Fin 2) (Fin 2) F) (c : F) :
    M * (c • A) * M⁻¹ = c • (M * A * M⁻¹) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

lemma conj_one' {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F) (hMd : IsUnit M.det) :
    M * 1 * M⁻¹ = 1 := by
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv M hMd]

/-- If `w ∈ SL(2,F)` conjugates the traceless part of `x` to its negative, then it inverts `x`:
`w * x * w⁻¹ = x⁻¹`. -/
theorem conj_eq_inv_of_conjNeg (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x w : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x ≠ 0)
    (hw : conjNeg F w (conjMat F x)) : w * x * w⁻¹ = x⁻¹ := by
  set M : Matrix (Fin 2) (Fin 2) F :=
    ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  set X : Matrix (Fin 2) (Fin 2) F :=
    ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hX
  set t : F := X.trace with ht
  have hMd : IsUnit M.det := by rw [hM, Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hW : conjMat F x = (2 : F) • X - t • 1 := by
    rw [conjMat, ← ht, ← hX]
  have hXdet : X.det = 1 := by rw [hX]; exact Matrix.SpecialLinearGroup.det_coe x
  have hCH : X * X = t • X - 1 := by
    have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F X
    rw [← ht, hXdet, one_smul] at h
    exact h
  have hconjW : M * conjMat F x * M⁻¹ = -conjMat F x := hw
  have hconjX : M * X * M⁻¹ = t • 1 - X := by
    have hW' : (2 : F) • X = conjMat F x + t • 1 := by
      rw [hW]; abel
    have hkey : -conjMat F x + t • 1 = (2 : F) • (t • 1 - X) := by
      have h1 : -(conjMat F x) + t • 1 = -((2 : F) • X) + (t • 1 + t • 1) := by
        rw [hW]; abel
      rw [h1, smul_sub, smul_smul, two_mul, add_smul]
      abel
    have htwo : (2 : F) • (M * X * M⁻¹) = (2 : F) • (t • 1 - X) := by
      calc (2 : F) • (M * X * M⁻¹)
          = M * ((2 : F) • X) * M⁻¹ := by rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = M * (conjMat F x + t • 1) * M⁻¹ := by rw [hW']
        _ = M * conjMat F x * M⁻¹ + M * (t • 1) * M⁻¹ := by
              rw [Matrix.mul_add, Matrix.add_mul]
        _ = -conjMat F x + t • 1 := by rw [hconjW, conj_smul', conj_one' M hMd]
        _ = (2 : F) • (t • 1 - X) := hkey
    have hcancel := congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => (2 : F)⁻¹ • Y) htwo
    simp only [smul_smul, inv_mul_cancel₀ h2, one_smul] at hcancel
    exact hcancel
  have hcoe : (((w * x * w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) = M * X * M⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ← hM, ← hX,
      adjugate_eq_inv_of_det_eq_one' M (by rw [hM, Matrix.SpecialLinearGroup.det_coe])]
  have hxinv : (((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) = t • 1 - X := by
    have hmul : X * (t • (1 : Matrix (Fin 2) (Fin 2) F) - X) = 1 := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hCH]
      module
    have hdet : (t • (1 : Matrix (Fin 2) (Fin 2) F) - X).det = 1 := by
      have h := congrArg Matrix.det hmul
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.det_one, one_mul] at h
      exact h
    set y : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨t • (1 : Matrix (Fin 2) (Fin 2) F) - X, hdet⟩ with hydef
    have hy : x * y = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
        show ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          t • (1 : Matrix (Fin 2) (Fin 2) F) - X from rfl]
      exact hmul
    have hyinv : y = x⁻¹ := eq_inv_of_mul_eq_one_right hy
    rw [← hyinv]
  apply Subtype.ext
  rw [hcoe, hconjX, hxinv]

end Work.L2F.Torus
