import Mathlib
import Submission.Work.PSL2.Basic

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

namespace Work.ZASS

/-- **PSL on the projective line, affine chart.**  The upper unipotent element
`Work.PSL2.pslUnipotent F b` (the image of `!![1,b;0,1]` in `PSL(2,F)`) acts on the affine chart
`t = x₀/x₁` by translation: `t ↦ t + b`.  Needed for step Z6.5 of area ZASS, where the image of
the unipotent group `U` in `PSL(2,E)` is identified with the translations. -/
theorem psl_smul_ptOf_unipotent (F : Type) [Field F] (b t : F) :
    Work.PSL2.pslUnipotent F b • Work.PSL2.ptOf F t = Work.PSL2.ptOf F (t + b) := by
  have hvec : SpecialLinearGroup.toLin' (Work.PSL2.unipotent F b) ![t, 1] = ![t + b, 1] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_unipotent]
    ext i
    fin_cases i <;> simp [Matrix.mulVec]
  change ((Work.PSL2.unipotent F b : SpecialLinearGroup (Fin 2) F) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptOf F t =
      Work.PSL2.ptOf F (t + b)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Work.PSL2.ptOf, Projectivization.smul_mk, Work.PSL2.ptOf]
  change Projectivization.mk F
      (SpecialLinearGroup.toLin' (Work.PSL2.unipotent F b) ![t, 1]) _ =
    Projectivization.mk F ![t + b, 1] _
  refine (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul]
  exact hvec.symm

/-- **PSL on the projective line, affine chart.**  The diagonal element
`Work.PSL2.pslDiag F a` (the image of `!![a,0;0,a⁻¹]` in `PSL(2,F)`) acts on the affine chart
`t = x₀/x₁` by `t ↦ a²t`.  Needed for step Z6.5 of area ZASS. -/
theorem psl_smul_ptOf_diag (F : Type) [Field F] (a : Fˣ) (t : F) :
    Work.PSL2.pslDiag F a • Work.PSL2.ptOf F t =
      Work.PSL2.ptOf F ((a : F) ^ 2 * t) := by
  have hvec : SpecialLinearGroup.toLin' (Work.PSL2.diag F a) ![t, 1] =
      ((a⁻¹ : Fˣ) : F) • ![((a : F) ^ 2 * t), 1] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_diag]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, sq, mul_assoc]
  change ((Work.PSL2.diag F a : SpecialLinearGroup (Fin 2) F) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptOf F t =
      Work.PSL2.ptOf F ((a : F) ^ 2 * t)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Work.PSL2.ptOf, Projectivization.smul_mk, Work.PSL2.ptOf]
  change Projectivization.mk F
      (SpecialLinearGroup.toLin' (Work.PSL2.diag F a) ![t, 1]) _ =
    Projectivization.mk F ![((a : F) ^ 2 * t), 1] _
  exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨a⁻¹, hvec.symm⟩

/-- **PSL on the projective line, affine chart.**  The Weyl element `Work.PSL2.pslWeyl F` acts
on the affine chart `t = x₀/x₁` by `t ↦ -t⁻¹`.  Needed for step Z6.5 of area ZASS. -/
theorem psl_smul_ptOf_weyl (F : Type) [Field F] {t : F} (ht : t ≠ 0) :
    Work.PSL2.pslWeyl F • Work.PSL2.ptOf F t = Work.PSL2.ptOf F (-(t⁻¹)) := by
  have hvec : SpecialLinearGroup.toLin' (Work.PSL2.weyl F) ![t, 1] =
      ((-t : F)) • ![-(t⁻¹), 1] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_weyl]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, inv_mul_cancel₀ ht, mul_comm, mul_neg, neg_mul]
  change ((Work.PSL2.weyl F : SpecialLinearGroup (Fin 2) F) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptOf F t =
      Work.PSL2.ptOf F (-(t⁻¹))
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Work.PSL2.ptOf, Projectivization.smul_mk, Work.PSL2.ptOf]
  change Projectivization.mk F
      (SpecialLinearGroup.toLin' (Work.PSL2.weyl F) ![t, 1]) _ =
    Projectivization.mk F ![-(t⁻¹), 1] _
  exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    ⟨Units.mk0 (-t) (by simpa using ht), hvec.symm⟩

theorem ptOf_injective (F : Type) [Field F] : Function.Injective (Work.PSL2.ptOf F) := by
  intro t u h
  rw [Work.PSL2.ptOf, Work.PSL2.ptOf] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F ![t, 1] ![u, 1] (by simp) (by simp)).mp h
  have h1 : (a : F) * 1 = 1 := congrFun ha 1
  have h0 : (a : F) * u = t := congrFun ha 0
  rw [mul_one] at h1
  rw [h1, one_mul] at h0
  exact h0.symm

theorem ptOf_ne_ptInf (F : Type) [Field F] (t : F) : Work.PSL2.ptOf F t ≠ Work.PSL2.ptInf F := by
  intro h
  rw [Work.PSL2.ptOf, Work.PSL2.ptInf] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F ![t, 1] ![1, 0] (by simp) (by simp)).mp h
  have h1 : (a : F) * 0 = 1 := congrFun ha 1
  simpa using h1

theorem pslUnipotent_smul_ptInf (F : Type) [Field F] (b : F) :
    Work.PSL2.pslUnipotent F b • Work.PSL2.ptInf F = Work.PSL2.ptInf F := by
  have hvec : SpecialLinearGroup.toLin' (Work.PSL2.unipotent F b) ![1, 0] = ![1, 0] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_unipotent]
    ext i
    fin_cases i <;> simp [Matrix.mulVec]
  change ((Work.PSL2.unipotent F b : SpecialLinearGroup (Fin 2) F) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptInf F = Work.PSL2.ptInf F
  simp only [Work.PSL2.ptInf]
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Projectivization.smul_mk]
  change Projectivization.mk F
      (SpecialLinearGroup.toLin' (Work.PSL2.unipotent F b) ![1, 0]) _ =
    Projectivization.mk F ![1, 0] _
  exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨1, by rw [one_smul]; exact hvec.symm⟩

theorem pslDiag_smul_ptInf (F : Type) [Field F] (a : Fˣ) :
    Work.PSL2.pslDiag F a • Work.PSL2.ptInf F = Work.PSL2.ptInf F := by
  have hvec : (a : F) • (![1, 0] : Fin 2 → F) =
      SpecialLinearGroup.toLin' (Work.PSL2.diag F a) ![1, 0] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_diag]
    ext i
    fin_cases i <;> simp [Matrix.mulVec]
  change ((Work.PSL2.diag F a : SpecialLinearGroup (Fin 2) F) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptInf F = Work.PSL2.ptInf F
  simp only [Work.PSL2.ptInf]
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Projectivization.smul_mk]
  change Projectivization.mk F
      (SpecialLinearGroup.toLin' (Work.PSL2.diag F a) ![1, 0]) _ =
    Projectivization.mk F ![1, 0] _
  exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨a, hvec⟩

theorem pslUnipotent_smul_ptZero (F : Type) [Field F] (b : F) :
    Work.PSL2.pslUnipotent F b • Work.PSL2.ptZero F = Work.PSL2.ptOf F b := by
  have hvec : SpecialLinearGroup.toLin' (Work.PSL2.unipotent F b) ![0, 1] = ![b, 1] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_unipotent]
    ext i
    fin_cases i <;> simp [Matrix.mulVec]
  change ((Work.PSL2.unipotent F b : SpecialLinearGroup (Fin 2) F) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptZero F = Work.PSL2.ptOf F b
  simp only [Work.PSL2.ptZero, Work.PSL2.ptOf]
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def,
    Projectivization.smul_mk]
  change Projectivization.mk F
      (SpecialLinearGroup.toLin' (Work.PSL2.unipotent F b) ![0, 1]) _ =
    Projectivization.mk F ![b, 1] _
  exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨1, by rw [one_smul]; exact hvec.symm⟩

end Work.ZASS
