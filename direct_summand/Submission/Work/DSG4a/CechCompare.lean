import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.BaseChange
import Submission.Work.DSG4a.SectionBaseChange
import Submission.Work.DSG4a.sectionBaseChange_bijective
import Submission.Work.DSG4a.sectionBaseChange_naturality
import Submission.Work.DSG4a.phiU_baseChange
import Submission.Work.DSG4a.BaseChangeComplex
import Submission.Work.DSG4a.CechBaseChange
import Submission.Work.DSG4a.tensorPi_extendScalars
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechComponents

/-!
# DSG4a: the termwise base change comparison of the Čech complex

This file builds the *termwise* comparison morphism of the base change of a Čech complex.  For
an algebra `A → A'`, a scheme `X` over `Spec A` with `X' = X ×_{Spec A} Spec A'`, a family of
opens `U : ι → X.Opens` and the pulled-back family `U' i = baseChangeOpen X f (U i)`, the
comparison is the morphism

`baseChangeComplex (cechZ A X f U) ⟶ cechZ A' X' f' U'`

whose degree-`n` component is, on each factor `x : Fin (n+1) → ι` of the Čech product, the map
`A' ⊗[A] Γ(X, Eobj U n x) ⟶ Γ(X', Eobj U' n x)` induced by `sectionBaseChange`.

The construction uses the adjunction `ModuleCat.extendRestrictScalarsAdj` (extension of scalars
is left adjoint to restriction of scalars), which turns the `A`-linear map
`Γ(X,U) → Γ(X',U')`, `g ↦ sectionBaseChange (g ⊗ 1)`, into an `A'`-linear map out of the
base-changed term.  The remaining steps (this file's `cechCompareN` and the `ℤ`-indexed
statement, with the coaugmentation compatibility) are described in `DESIGN_cechCompare.md`.

-/

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace Work.DSG4a

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

section Termwise

variable (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- The `A'`-module `A' ⊗[A] Γ(X,U)`: the term of the base-changed Čech complex attached to the
open `U`. -/
noncomputable abbrev bcTerm (U : X.Opens) : ModuleCat.{u} A' :=
  (ModuleCat.extendScalars (algebraMap A A')).obj
    ((DSMap.cechPresheaf A X f).obj (Opposite.op U))

/-- The `A'`-module `Γ(X', U')`, the corresponding term on the base-changed scheme. -/
noncomputable abbrev bcrTerm (U : X.Opens) : ModuleCat.{u} A' :=
  (DSMap.cechPresheaf A' (baseChangeScheme (A := A) (A' := A') X f)
    (baseChangeSnd (A := A) (A' := A') X f)).obj
    (Opposite.op (baseChangeOpen (A := A) (A' := A') X f U))

/-- The `A`-algebra structure `A → Γ(X,U)` used by `sectionBaseChange`. -/
noncomputable abbrev bcAlgΓ0 (U : X.Opens) : Algebra A Γ(X, U) :=
  (DSMap.phiU A X f U).toAlgebra

/-- The `A'`-algebra structure `A' → Γ(X',U')` used by `sectionBaseChange`. -/
noncomputable abbrev bcAlgΓ1 (U : X.Opens) : Algebra A'
    Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
  (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
    (baseChangeSnd (A := A) (A' := A') X f)
    (baseChangeOpen (A := A) (A' := A') X f U)).toAlgebra

/-- The `A`-algebra structure on `Γ(X',U')` obtained by composing the two structure maps
(`phiU_baseChange` says that this is the structure against which `sectionBaseChange` is
`A`-linear). -/
noncomputable abbrev bcAlgΓ2 (U : X.Opens) : Algebra A
    Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
  ((DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
    (baseChangeSnd (A := A) (A' := A') X f)
    (baseChangeOpen (A := A) (A' := A') X f U)).comp (algebraMap A A')).toAlgebra

end Termwise

/-- The `A`-linear map `Γ(X,U) ⟶ Γ(X',U')`, `g ↦ sectionBaseChange (g ⊗ 1)`.  This is the
input of the adjunction `extendRestrictScalarsAdj` from which the `A'`-linear comparison map of
a single Čech term is obtained. -/
noncomputable def sectionBaseChangeLin (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) :
    (DSMap.cechPresheaf A X f).obj (Opposite.op U) ⟶
      (ModuleCat.restrictScalars (algebraMap A A')).obj (bcrTerm (A := A) (A' := A') X f U) := by
  letI : Algebra A Γ(X, U) := bcAlgΓ0 (A := A) X f U
  letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) := bcAlgΓ1 (A := A) (A' := A') X f U
  letI : Module A Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
    @Module.compHom A' A Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) _ _ inferInstance _ (algebraMap A A')
  let lm : Γ(X, U) →ₗ[A] Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
    { toFun := fun g => sectionBaseChange (A := A) (A' := A') X f U
        (TensorProduct.mk A Γ(X, U) A' g 1)
      map_add' := by
        intro x y
        show sectionBaseChange (A := A) (A' := A') X f U
            (TensorProduct.mk A Γ(X, U) A' (x + y) 1) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro a g
        have hkey : ((algebraMap A Γ(X, U)) a * g) ⊗ₜ[A] (1 : A') =
            ((algebraMap A Γ(X, U)) a ⊗ₜ[A] (1 : A')) * (g ⊗ₜ[A] (1 : A')) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul ((algebraMap A Γ(X, U)) a) g (1 : A') (1 : A')]
          rw [mul_one]
        have hkey' : TensorProduct.mk A Γ(X, U) A' ((algebraMap A Γ(X, U)) a * g) 1 =
            TensorProduct.mk A Γ(X, U) A' ((algebraMap A Γ(X, U)) a) 1 *
              TensorProduct.mk A Γ(X, U) A' g 1 := by
          simp only [TensorProduct.mk_apply]
          exact hkey
        show sectionBaseChange (A := A) (A' := A') X f U
            (TensorProduct.mk A Γ(X, U) A' (algebraMap A Γ(X, U) a * g) 1) =
          (RingHom.id A) a • sectionBaseChange (A := A) (A' := A') X f U
            (TensorProduct.mk A Γ(X, U) A' g 1)
        rw [hkey', map_mul,
          sectionBaseChange_tmul (A := A) (A' := A') X f U ((algebraMap A Γ(X, U)) a) 1]
        rw [map_one (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
          (baseChangeSnd (A := A) (A' := A') X f)
          (baseChangeOpen (A := A) (A' := A') X f U)), mul_one]
        rw [show (algebraMap A Γ(X, U)) a = (DSMap.phiU A X f U) a from rfl]
        rw [phiU_baseChange (A := A) (A' := A') X f U a]
        rw [show (RingHom.id A) a • (sectionBaseChange (A := A) (A' := A') X f U
              (TensorProduct.mk A Γ(X, U) A' g 1)) =
            (algebraMap A A' a) • (sectionBaseChange (A := A) (A' := A') X f U
              (TensorProduct.mk A Γ(X, U) A' g 1)) from rfl]
        rw [Algebra.smul_def]
        rfl }
  exact ModuleCat.ofHom (X := Γ(X, U))
    (Y := Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U)) lm

/-- **The base change comparison of a single Čech term.**  The `A'`-linear map
`A' ⊗[A] Γ(X,U) ⟶ Γ(X',U')` sending `1 ⊗ g` to `sectionBaseChange (g ⊗ 1)`, obtained from
`sectionBaseChangeLin` through the adjunction `extendRestrictScalarsAdj` (extension of scalars
is left adjoint to restriction of scalars). -/
noncomputable def sectionBaseChangeA' (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) :
    bcTerm (A := A) (A' := A') X f U ⟶ bcrTerm (A := A) (A' := A') X f U :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap A A')).homEquiv
      ((DSMap.cechPresheaf A X f).obj (Opposite.op U))
      (bcrTerm (A := A) (A' := A') X f U)).symm
    (sectionBaseChangeLin (A := A) (A' := A') X f U)

/-- The computation rule of the comparison map on a pure tensor: `1 ⊗ g ↦ sectionBaseChange
(g ⊗ 1)`. -/
theorem sectionBaseChangeA'_tmul (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    (g : Γ(X, U)) :
    (sectionBaseChangeA' (A := A) (A' := A') X f U)
        ((1 : A') ⊗ₜ[A, algebraMap A A'] g) =
      (letI : Algebra A Γ(X, U) := bcAlgΓ0 (A := A) X f U
       letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
        baseChangeOpen (A := A) (A' := A') X f U) := bcAlgΓ1 (A := A) (A' := A') X f U
       sectionBaseChange (A := A) (A' := A') X f U (TensorProduct.mk A Γ(X, U) A' g 1)) := by
  letI : Algebra A Γ(X, U) := bcAlgΓ0 (A := A) X f U
  letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) := bcAlgΓ1 (A := A) (A' := A') X f U
  have h := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (f := algebraMap A A') (M := (DSMap.cechPresheaf A X f).obj (Opposite.op U))
    (N := bcrTerm (A := A) (A' := A') X f U)
    (φ := sectionBaseChangeA' (A := A) (A' := A') X f U) g
  simp only [sectionBaseChangeA', Equiv.apply_symm_apply] at h
  exact h.symm

end Work.DSG4a
