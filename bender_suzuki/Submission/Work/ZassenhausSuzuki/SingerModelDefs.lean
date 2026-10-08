import Mathlib
import Submission.Work.Hering.AppVIII.QuadExtNorm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Singer-cycle model in `SL(2, F)`: vocabulary

This file fixes the objects used to build the *non-split torus* (Singer cycle) of `SL(2, F)`
for `F` a finite field of characteristic two, inside the quadratic extension
`E = QuadExt F ε = F[α]`, `α² = εα + 1` (Peterfalvi I, Appendix VIII).

* `qalphaMat ε` — the matrix of multiplication by `α` in the `F`-basis `(1, α)`, namely
  `!![0, 1; 1, ε]`;
* `quadAlgHom ε : QuadExt F ε →ₐ[F] M₂(F)` — the *regular representation* (matrix of
  multiplication by `x` in the basis `(1, α)`), an injective `F`-algebra homomorphism;
* `det_quadAlgHom` — `det (quadAlgHom ε x) = Algebra.norm F x`;
* `normOne ε` — the norm-one subgroup of `Eˣ` (of order `|F| + 1`);
* `singerSubgroup ε` — its image in `SL(2, F)`.

`det_quadAlgHom` shows that `normOne` lands in `SL(2, F)`; the image is the Singer cycle.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Polynomial Matrix
open Work.Hering.AppVIII

namespace Work.ZassenhausSuzuki

variable {F : Type*} [Field F] [CharP F 2]

/-- The companion matrix of `X² + εX + 1`: the matrix of multiplication by the root `α` of
`quadPoly F ε` in the basis `(1, α)` of `QuadExt F ε`. -/
def qalphaMat (ε : F) : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, ε]

@[simp] theorem qalphaMat_trace (ε : F) : (qalphaMat ε).trace = ε := by
  simp [qalphaMat, Matrix.trace_fin_two]

@[simp] theorem qalphaMat_det (ε : F) : (qalphaMat ε).det = 1 := by
  simp [qalphaMat, Matrix.det_fin_two, CharTwo.neg_eq]

theorem qalphaMat_sq (ε : F) : qalphaMat ε * qalphaMat ε = ε • qalphaMat ε + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qalphaMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The regular representation of the quadratic extension: the matrix of multiplication by `x`
in the `F`-basis `(1, α)`. -/
noncomputable def quadAlgHom (ε : F) : QuadExt F ε →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
  (LinearMap.toMatrixAlgEquiv (qbasis F ε)).toAlgHom.comp (Algebra.lmul F (QuadExt F ε))

theorem quadAlgHom_apply (ε : F) (x : QuadExt F ε) (i j : Fin 2) :
    quadAlgHom ε x i j = (qbasis F ε).repr (x * qbasis F ε j) i := by
  rw [quadAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    show (LinearMap.toMatrixAlgEquiv (qbasis F ε)) ((Algebra.lmul F (QuadExt F ε)) x)
        = LinearMap.toMatrix (qbasis F ε) (qbasis F ε) ((Algebra.lmul F (QuadExt F ε)) x)
      from by ext i j; rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]]
  rw [LinearMap.toMatrix_apply]
  rfl

/-- **The determinant of the regular representation is the field norm.** -/
theorem det_quadAlgHom (ε : F) (x : QuadExt F ε) :
    (quadAlgHom ε x).det = Algebra.norm F x := by
  rw [quadAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    show (LinearMap.toMatrixAlgEquiv (qbasis F ε)) ((Algebra.lmul F (QuadExt F ε)) x)
        = LinearMap.toMatrix (qbasis F ε) (qbasis F ε) ((Algebra.lmul F (QuadExt F ε)) x)
      from by ext i j; rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]]
  rw [LinearMap.det_toMatrix, ← Algebra.norm_apply]

theorem quadAlgHom_injective (ε : F) : Function.Injective (quadAlgHom ε) := by
  intro x y h
  have h' : (Algebra.lmul F (QuadExt F ε)) x = (Algebra.lmul F (QuadExt F ε)) y :=
    (LinearMap.toMatrixAlgEquiv (qbasis F ε)).injective h
  have h3 := congrArg (fun f : QuadExt F ε →ₗ[F] QuadExt F ε => f 1) h'
  simpa using h3

theorem quadAlgHom_qalpha (ε : F) : quadAlgHom ε (qalpha F ε) = qalphaMat ε := by
  have hsq : qalpha F ε * qalpha F ε = ε • qalpha F ε + 1 := by
    rw [qalpha_sq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  ext i j
  rw [quadAlgHom_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [qalphaMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_zero, Fin.mk_one]
  · rw [← qbasis_one F ε, qbasis_zero, mul_one, Module.Basis.repr_self_apply]; simp
  · rw [qbasis_one F ε, hsq, ← qbasis_one F ε, ← qbasis_zero F ε]
    rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    simp
  · rw [← qbasis_one F ε, qbasis_zero, mul_one, Module.Basis.repr_self_apply]; simp
  · rw [qbasis_one F ε, hsq, ← qbasis_one F ε, ← qbasis_zero F ε]
    rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    simp

/-! ## The norm-one subgroup and the Singer cycle -/

/-- The norm `Eˣ → Fˣ` of the quadratic extension. -/
noncomputable def normUnitHom (ε : F) : (QuadExt F ε)ˣ →* Fˣ :=
  Units.map (Algebra.norm F)

@[simp] theorem normUnitHom_apply (ε : F) (x : (QuadExt F ε)ˣ) :
    ((normUnitHom ε x : Fˣ) : F) = Algebra.norm F (x : QuadExt F ε) := rfl

/-- The norm-one subgroup of `Eˣ`; for `E = GF(q²)` it is cyclic of order `q + 1`. -/
noncomputable def normOne (ε : F) : Subgroup (QuadExt F ε)ˣ := (normUnitHom ε).ker

theorem mem_normOne_iff (ε : F) (x : (QuadExt F ε)ˣ) :
    x ∈ normOne ε ↔ Algebra.norm F (x : QuadExt F ε) = 1 := by
  rw [normOne, MonoidHom.mem_ker, normUnitHom]
  constructor
  · intro h; simpa using Units.ext_iff.mp h
  · intro h; exact Units.ext (by simpa using h)

/-- The norm-one subgroup of `Eˣ`, mapped into `SL(2, F)` through the regular representation. -/
noncomputable def normOneToSL (ε : F) :
    ↥(normOne ε) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun x :=
    ⟨quadAlgHom ε (((x : (QuadExt F ε)ˣ) : QuadExt F ε)),
      by rw [det_quadAlgHom, (mem_normOne_iff ε _).mp x.2]⟩
  map_one' := by
    apply Subtype.ext
    show quadAlgHom ε ((((1 : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε))
        = (1 : Matrix (Fin 2) (Fin 2) F)
    rw [show ((((1 : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)) = 1 from rfl, map_one]
  map_mul' := by
    intro a b
    apply Subtype.ext
    show quadAlgHom ε ((((a * b : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε))
        = quadAlgHom ε (((a : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)
          * quadAlgHom ε (((b : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)
    rw [show ((((a * b : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε))
        = (((a : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)
          * (((b : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε) from rfl]
    rw [map_mul]

/-- **The Singer cycle**: the image of the norm-one subgroup in `SL(2, F)`. -/
noncomputable def singerSubgroup (ε : F) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (normOneToSL ε).range

theorem singerSubgroup_def (ε : F) :
    singerSubgroup ε = (normOneToSL ε).range := rfl

end Work.ZassenhausSuzuki
