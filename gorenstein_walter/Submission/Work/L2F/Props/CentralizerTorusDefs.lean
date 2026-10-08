import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

variable (F : Type*) [Field F]

/-- The traceless part `g - (tr g / 2) • 1` of `g ∈ GL(2,F)`. -/
noncomputable def glW (g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  (g : Matrix (Fin 2) (Fin 2) F) - ((g : Matrix (Fin 2) (Fin 2) F).trace / 2) • 1

/-- The discriminant `(tr g / 2) ^ 2 - det g` of `g ∈ GL(2,F)`. -/
noncomputable def glD (g : GL (Fin 2) F) : F :=
  ((g : Matrix (Fin 2) (Fin 2) F).trace / 2) ^ 2 - (g : Matrix (Fin 2) (Fin 2) F).det

/-- The "squaring" map `det(h)^{-1} • (h * h)` on `GL(2,F)`; for commuting `h` it is the
composition of `h ↦ h / conj h` with the identification `F[h] ≅ F[X]/(X² - glD)`, and it lands in
`SL(2,F)`. -/
noncomputable def rhoMat (h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  ((h : Matrix (Fin 2) (Fin 2) F).det)⁻¹ • ((h : Matrix (Fin 2) (Fin 2) F) *
    (h : Matrix (Fin 2) (Fin 2) F))

@[simp]
theorem glW_apply (g : GL (Fin 2) F) :
    glW F g = (g : Matrix (Fin 2) (Fin 2) F) -
      ((g : Matrix (Fin 2) (Fin 2) F).trace / 2) • 1 := rfl

@[simp]
theorem glD_apply (g : GL (Fin 2) F) :
    glD F g = ((g : Matrix (Fin 2) (Fin 2) F).trace / 2) ^ 2 -
      (g : Matrix (Fin 2) (Fin 2) F).det := rfl

/-- `g = λ • 1 + glW F g` with `λ = tr g / 2`. -/
theorem glW_add (g : GL (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) = ((g : Matrix (Fin 2) (Fin 2) F).trace / 2) • 1 + glW F g := by
  rw [glW_apply]; abel

/-- The traceless part is traceless. -/
theorem glW_trace (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F) : (glW F g).trace = 0 := by
  rw [glW_apply, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  simp only [smul_eq_mul, Nat.cast_ofNat]
  exact sub_eq_zero.mpr (div_mul_cancel₀ _ h2).symm

/-- `glW F g * glW F g = glD F g • 1`. -/
theorem glW_mul_self (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F) :
    glW F g * glW F g = glD F g • 1 := by
  rw [glW_apply, glD_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] <;>
    field_simp <;> ring

/-- `det (rhoMat F h) = 1`. -/
theorem rhoMat_det (h : GL (Fin 2) F) : (rhoMat F h).det = 1 := by
  rw [rhoMat, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, sq]
  have hu : ((h : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det h).ne_zero
  field_simp

/-- `rhoMat F h` as an element of `SL(2,F)`. -/
noncomputable def rhoSL (h : GL (Fin 2) F) : SL(2, F) := ⟨rhoMat F h, rhoMat_det F h⟩

@[simp]
theorem rhoSL_coe (h : GL (Fin 2) F) :
    ((rhoSL F h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = rhoMat F h := rfl

theorem rhoSL_one : rhoSL F (1 : GL (Fin 2) F) = 1 := by
  apply Subtype.ext
  rw [rhoSL_coe, rhoMat, Matrix.GeneralLinearGroup.coe_one, Matrix.det_one, inv_one,
    Matrix.mul_one, one_smul, Matrix.SpecialLinearGroup.coe_one]

end Work.L2F.Props
