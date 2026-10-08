import Mathlib
import Submission.Work.DSTR.M110.torusFrobDefs

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial Matrix

namespace Work.DSTR.M110

/-- Conjugation by a unit of `GL(2,F)`, as a ring endomorphism of `M₂(F)`:
`x ↦ S * x * S⁻¹`. -/
noncomputable def conjMatRingHom {F : Type*} [Field F] (S : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F →+* Matrix (Fin 2) (Fin 2) F where
  toFun x := (S : Matrix (Fin 2) (Fin 2) F) * x * (S : Matrix (Fin 2) (Fin 2) F)⁻¹
  map_one' := by
    rw [mul_one]
    have h : (S : Matrix (Fin 2) (Fin 2) F) * ((S : Matrix (Fin 2) (Fin 2) F))⁻¹ = 1 := by
      have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
        (mul_inv_cancel S)
      rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
           Matrix.GeneralLinearGroup.coe_one] at h2
    exact h
  map_mul' := by
    have hSS : ((S : Matrix (Fin 2) (Fin 2) F))⁻¹ * (S : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
        (inv_mul_cancel S)
      rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
           Matrix.GeneralLinearGroup.coe_one] at h2
    intro x y
    calc (S : Matrix (Fin 2) (Fin 2) F) * (x * y) * (S : Matrix (Fin 2) (Fin 2) F)⁻¹
        = (S : Matrix (Fin 2) (Fin 2) F) * x * y * (S : Matrix (Fin 2) (Fin 2) F)⁻¹ := by
          noncomm_ring
      _ = (S : Matrix (Fin 2) (Fin 2) F) * x * ((S : Matrix (Fin 2) (Fin 2) F)⁻¹ *
            (S : Matrix (Fin 2) (Fin 2) F)) * y * (S : Matrix (Fin 2) (Fin 2) F)⁻¹ := by
          rw [hSS]; noncomm_ring
      _ = ((S : Matrix (Fin 2) (Fin 2) F) * x * (S : Matrix (Fin 2) (Fin 2) F)⁻¹) *
            ((S : Matrix (Fin 2) (Fin 2) F) * y * (S : Matrix (Fin 2) (Fin 2) F)⁻¹) := by
          noncomm_ring
  map_zero' := by simp
  map_add' := by
    intro x y
    rw [mul_add, add_mul]

/-- Conjugation fixes scalar multiples of the identity. -/
lemma conjMatRingHom_smul_one {F : Type*} [Field F] (S : GL (Fin 2) F) (a : F) :
    conjMatRingHom S (a • 1 : Matrix (Fin 2) (Fin 2) F) = a • 1 := by
  have h : (S : Matrix (Fin 2) (Fin 2) F) * ((S : Matrix (Fin 2) (Fin 2) F))⁻¹ = 1 := by
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      (mul_inv_cancel S)
    rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
         Matrix.GeneralLinearGroup.coe_one] at h2
  show (S : Matrix (Fin 2) (Fin 2) F) * (a • 1) * (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = a • 1
  rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, h]

/-- Change of basis intertwines the two algebra structures: conjugation by `S` carries
`torusAlgHom B c hB` into `torusAlgHom B' c hB'` whenever `S B S⁻¹ = B'`. -/
lemma torusAlgHom_conj_hom {F : Type*} [Field F] [DecidableEq F]
    (B B' : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)
    (hB' : (B' : Matrix (Fin 2) (Fin 2) F) * B' = c • 1)
    (S : GL (Fin 2) F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
        (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = (B' : Matrix (Fin 2) (Fin 2) F)) :
    torusAlgHom B' c hB' = (conjMatRingHom S).comp (torusAlgHom B c hB) := by
  apply AdjoinRoot.ringHom_ext
  · ext a
    simp only [RingHom.comp_apply]
    rw [← AdjoinRoot.algebraMap_eq, torusAlgHom_of, torusAlgHom_of, conjMatRingHom_smul_one]
  · simp only [RingHom.comp_apply]
    rw [torusAlgHom_root, torusAlgHom_root]
    exact hS.symm

/-- Pointwise form of `torusAlgHom_conj_hom`. -/
lemma torusAlgHom_conj {F : Type*} [Field F] [DecidableEq F]
    (B B' : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)
    (hB' : (B' : Matrix (Fin 2) (Fin 2) F) * B' = c • 1)
    (S : GL (Fin 2) F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
        (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = (B' : Matrix (Fin 2) (Fin 2) F))
    (μ : AdjoinRoot (X ^ 2 - C c : F[X])) :
    torusAlgHom B' c hB' μ = conjMatRingHom S (torusAlgHom B c hB μ) := by
  rw [torusAlgHom_conj_hom B B' c hB hB' S hS]
  rfl

/-- Change of basis conjugates the matrix torus: `torusGL B' c hB' u = S (torusGL B c hB u)
S⁻¹`. -/
lemma torusGL_conj {F : Type*} [Field F] [DecidableEq F]
    (B B' : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)
    (hB' : (B' : Matrix (Fin 2) (Fin 2) F) * B' = c • 1)
    (S : GL (Fin 2) F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
        (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = (B' : Matrix (Fin 2) (Fin 2) F))
    (u : TorUnits F c) :
    torusGL B' c hB' u = S * torusGL B c hB u * S⁻¹ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv]
  simp only [torusGL, Units.coe_map]
  exact torusAlgHom_conj B B' c hB hB' S hS (u : _)

/-- The permutation representation of `PGL(2,F)` intertwines conjugation with conjugation. -/
lemma pglHom_conj {F : Type*} [Field F] [DecidableEq F] (S T : GL (Fin 2) F) :
    Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk (S * T * S⁻¹)) =
      Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S) *
        Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk T) *
        (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S))⁻¹ := by
  rw [show Matrix.ProjGenLinGroup.mk (S * T * S⁻¹) =
      Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk T *
        (Matrix.ProjGenLinGroup.mk S)⁻¹ by
      rw [map_mul, map_mul, map_inv]]
  rw [map_mul, map_mul, map_inv]

theorem torusPermConjProof {F : Type*} [Field F] [DecidableEq F]
    (B B' : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)
    (hB' : (B' : Matrix (Fin 2) (Fin 2) F) * B' = c • 1)
    (S : GL (Fin 2) F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
        (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = (B' : Matrix (Fin 2) (Fin 2) F))
    (u : Work.DSTR.M110.TorUnits F c) :
    Work.DSTR.M110.torusPerm B' c hB' u =
      Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S) *
          Work.DSTR.M110.torusPerm B c hB u *
        (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk S))⁻¹ := by
  rw [torusPerm_apply, torusPerm_apply, torusGL_conj B B' c hB hB' S hS u]
  exact pglHom_conj S (torusGL B c hB u)

end Work.DSTR.M110
