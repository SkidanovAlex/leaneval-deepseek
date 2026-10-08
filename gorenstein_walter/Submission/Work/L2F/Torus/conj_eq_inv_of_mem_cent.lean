import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Torus.mem_centralizer_iff

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-- The inverse of `A ∈ SL(2,F)`, read as a matrix, is the matrix inverse of `A`: indeed
`↑A⁻¹ = adjugate ↑A` (`Matrix.SpecialLinearGroup.coe_inv`) and `adjugate ↑A = (↑A)⁻¹` because
`det ↑A = 1` is a unit. -/
theorem coe_inv_sl (F : Type*) [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (((A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv,
    Matrix.inv_eq_left_inv (B := ((A : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).adjugate) ?_]
  rw [Matrix.adjugate_mul, Matrix.SpecialLinearGroup.det_coe, one_smul]

/-- If `w ∈ SL(2,F)` conjugates the traceless part of `x` to its negative, then `w` inverts every
element of the centralizer of `x` in `SL(2,F)`. -/
theorem conj_eq_inv_of_mem_cent (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (x w c : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x ≠ 0) (hw : conjNeg F w (conjMat F x)) (hc : c ∈ cent F x) : w * c * w⁻¹ = c⁻¹ := by
  -- `c` is `a • 1 + b • W` with `W = conjMat F x` and `a ^ 2 - disc F x * b ^ 2 = 1`.
  obtain ⟨a, b, hab, hcmat⟩ := (mem_centralizer_iff F h2 x c hD).mp hc
  set W : Matrix (Fin 2) (Fin 2) F := conjMat F x with hW
  have hWsq : W * W = disc F x • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hW]; exact conjMat_mul_self F x
  have hWneg : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * W *
      (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))⁻¹ = -W := by
    rw [hW]; exact hw
  have hwdet : IsUnit
      (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det) := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hww : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hwdet
  -- Conjugation is `F`-linear, so it turns `a • 1 + b • W` into `a • 1 - b • W`.
  have hL : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (a • 1 + b • W) * (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))⁻¹
      = a • 1 - b • W := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, hWneg, hww, smul_neg]
    module
  -- And `a • 1 - b • W` is the matrix inverse of `a • 1 + b • W` since
  -- `(a • 1 + b • W) * (a • 1 - b • W) = (a ^ 2 - disc F x * b ^ 2) • 1 = 1`.
  have hR : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W)⁻¹ = a • 1 - b • W := by
    refine Matrix.inv_eq_right_inv ?_
    rw [show a • (1 : Matrix (Fin 2) (Fin 2) F) - b • W = a • 1 + (-b) • W from by
      rw [neg_smul, sub_eq_add_neg]]
    rw [Work.L2F.Mat2.smul_one_add_smul_mul hWsq a b a (-b)]
    have h1 : a * a + disc F x * (b * -b) = 1 := by linear_combination hab
    have h2 : a * -b + b * a = 0 := by ring
    rw [h1, h2]
    simp
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl F w,
    coe_inv_sl F c, hcmat, hL, hR]

end Work.L2F.Torus
