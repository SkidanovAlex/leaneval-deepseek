import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.mem_cmtK0_iff_exists

open scoped MatrixGroups

-- `hT2` (the hypothesis `T * T = -1`) is part of the intended setting but is not needed for this
-- computation, so no proof step refers to it.
set_option linter.unusedVariables false

namespace Work.L2F.Props

/-! ## Two matrix computations behind `conj_eq_inv_of_mem_cmtK0`

Everything here is elementary `2 × 2` matrix algebra over a field `F`, with the notation
`S` for the matrix, `lam` for the scalar with `S * S = lam • 1`. -/

/-- **The "norm" of `a • 1 + b • S`.**  If `S * S = lam • 1` then
`(a • 1 + b • S) * (a • 1 - b • S) = (a ^ 2 - lam * b ^ 2) • 1`. -/
lemma mul_smul_one_sub_smul (F : Type*) [Field F] (S : Matrix (Fin 2) (Fin 2) F) (lam a b : F)
    (hS : S * S = lam • 1) :
    (a • 1 + b • S) * (a • 1 - b • S) = (a ^ 2 - lam * b ^ 2) • 1 := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, hS, smul_add]
  rw [mul_comm b a]
  have hcancel : (a * a) • (1 : Matrix (Fin 2) (Fin 2) F) + (a * b) • S -
      ((a * b) • S + (b * (b * lam)) • 1) = (a * a) • 1 - (b * (b * lam)) • 1 := by abel
  rw [hcancel, ← sub_smul]
  have hs : a * a - b * (b * lam) = a ^ 2 - lam * b ^ 2 := by ring
  rw [hs]

/-- **The inverse of `a • 1 + b • S`.**  If `S * S = lam • 1`, `M = a • 1 + b • S` and
`a ^ 2 - lam * b ^ 2 = 1` then `a • 1 - b • S` is a right inverse of `M` (and, by
commutativity of the two summands, a two-sided one). -/
lemma mul_sub_smul_eq_one_of_sq_eq_smul_one (F : Type*) [Field F]
    (S M : Matrix (Fin 2) (Fin 2) F) (lam a b : F)
    (hS : S * S = lam • 1) (hM : M = a • 1 + b • S) (hab : a ^ 2 - lam * b ^ 2 = 1) :
    M * (a • 1 - b • S) = 1 := by
  rw [hM, mul_smul_one_sub_smul F S lam a b hS, hab, one_smul]

/-- **Conjugating `a • 1 + b • S` by a matrix inverting `S`.**  If `B * B⁻¹ = 1`,
`B * S * B⁻¹ = -S` and `M = a • 1 + b • S` then `B * M * B⁻¹ = a • 1 - b • S`. -/
lemma conj_smul_one_add_smul_eq (F : Type*) [Field F]
    (B M S : Matrix (Fin 2) (Fin 2) F) (a b : F)
    (hBB : B * B⁻¹ = 1) (hBS : B * S * B⁻¹ = -S) (hM : M = a • 1 + b • S) :
    B * M * B⁻¹ = a • 1 - b • S := by
  simp only [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hBS, hBB, smul_neg, sub_eq_add_neg]

/-- Elements of the centralizer torus `cmtK0 F S` are *inverted* by conjugation with `T`.
Hint: write `x = a • 1 + b • S` with `a² - lam·b² = 1` (`Work.L2F.Props.mem_cmtK0_iff_exists`);
then `T x T⁻¹ = a • 1 + b • (T S T⁻¹) = a • 1 - b • S = x⁻¹`, using `T S T⁻¹ = -S` (from `hST`) and
`(a • 1 + b • S) * (a • 1 - b • S) = (a² - lam·b²) • 1 = 1`.  Everything is a computation with
`Matrix` operations (`Matrix.add_mul`, `Matrix.mul_add`, `Matrix.neg_mul`, `Matrix.mul_neg`,
`Matrix.smul_mul`, `Matrix.mul_smul`, `Matrix.one_mul`, `Matrix.mul_one`); passing from `GL` to
matrices uses `Matrix.GeneralLinearGroup.coe_mul`, `coe_inv`, and `Units.ext`. -/
theorem conj_eq_inv_of_mem_cmtK0 (F : Type*) [Field F]
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
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
        (mul_sub_smul_eq_one_of_sq_eq_smul_one F S (x : Matrix (Fin 2) (Fin 2) F) lam a b
          hS hmat hab)
    rw [hxinv]
    exact conj_smul_one_add_smul_eq F (T : Matrix (Fin 2) (Fin 2) F)
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

end Work.L2F.Props
