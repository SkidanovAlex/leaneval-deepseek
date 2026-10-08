import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.mem_cmtK0_iff_exists
import Submission.Work.L2F.Props.conj_eq_inv_of_mem_cmtK0

namespace Work.L2F.Props.L2Outer

/-- An element `T` with `T S T⁻¹ = -S` (the `cmtK1` coset condition, here in commutation form)
inverts every element of the centralizer `cmtK0 F S`.

This is the same computation as `Work.L2F.Props.conj_eq_inv_of_mem_cmtK0`, but the extra
hypothesis `T * T = -1` is not needed.  If `x ∈ cmtK0 F S` then `x = a • 1 + b • S`
(`Work.L2F.Props.mem_cmtK0_iff_exists`), and `T x T⁻¹ = a • 1 + b • (T S T⁻¹) = a • 1 - b • S = x⁻¹`. -/
theorem conj_eq_inv_of_mem_cmtK1 (F : Type*) [Field F]
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hST : Matrix.SpecialLinearGroup.toGL T * S = Work.L2F.Props.negGL F S *
      Matrix.SpecialLinearGroup.toGL T)
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : x ∈ Work.L2F.Props.cmtK0 F S) :
    T * x * T⁻¹ = x⁻¹ := by
  -- write `x = a • 1 + b • S` with `a ^ 2 - lam * b ^ 2 = 1`
  obtain ⟨a, b, hab, hmat⟩ :=
    (Work.L2F.Props.mem_cmtK0_iff_exists F S lam hS hlam hns x).mp hx
  -- `T` inverts `S`: pass the commutation relation `hST` to matrices
  have hTS : (T : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) =
      -(S : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 2) F =>
      (u : Matrix (Fin 2) (Fin 2) F)) hST
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Work.L2F.Props.negGL,
      Work.L2F.Props.negOneGL_apply, Matrix.neg_mul, Matrix.one_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h
  -- `det T = 1`, so the matrix inverse of `T` exists
  have hTdet : IsUnit (T : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  -- hence `T * S * T⁻¹ = -S`
  have hconjS : (T : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) *
      (T : Matrix (Fin 2) (Fin 2) F)⁻¹ = -(S : Matrix (Fin 2) (Fin 2) F) := by
    rw [hTS, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv (T : Matrix (Fin 2) (Fin 2) F) hTdet, Matrix.mul_one]
  -- the matrix identity `T * x * T⁻¹ = x⁻¹`
  have hkey : (T : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
      (T : Matrix (Fin 2) (Fin 2) F)⁻¹ = (x : Matrix (Fin 2) (Fin 2) F)⁻¹ := by
    have hxinv : (x : Matrix (Fin 2) (Fin 2) F)⁻¹ =
        a • 1 - b • (S : Matrix (Fin 2) (Fin 2) F) :=
      Matrix.inv_eq_right_inv
        (Work.L2F.Props.mul_sub_smul_eq_one_of_sq_eq_smul_one F S
          (x : Matrix (Fin 2) (Fin 2) F) lam a b hS hmat hab)
    rw [hxinv]
    exact Work.L2F.Props.conj_smul_one_add_smul_eq F (T : Matrix (Fin 2) (Fin 2) F)
      (x : Matrix (Fin 2) (Fin 2) F) (S : Matrix (Fin 2) (Fin 2) F) a b
      (Matrix.mul_nonsing_inv _ hTdet) hconjS hmat
  -- transfer the matrix identity back to `SL(2,F) ⊂ GL(2,F)`
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, map_inv]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  exact hkey

end Work.L2F.Props.L2Outer
