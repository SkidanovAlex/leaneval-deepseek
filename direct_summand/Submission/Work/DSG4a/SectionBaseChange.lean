import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.BaseChange
import Submission.Work.DSG4a.phiU_baseChange

/-!
# DSG4a: the comparison map of the flat base change of sections

Let `f : X ⟶ Spec A` be a morphism of schemes, `A → A'` an algebra, `X_{A'} = X ×_{Spec A} Spec A'`
its base change (`baseChangeScheme`, `baseChangeFst`, `baseChangeSnd`, `baseChangeOpen` in
`Submission.Work.DSG4a.BaseChange`), and `U ⊆ X` an open.

The `A'`-algebra `Γ(X_{A'}, U_{A'})` receives ring maps from `Γ(X,U)` (pullback of sections
along `baseChangeFst`) and from `A'` (the structure map through `baseChangeSnd`), which agree on
`A` (`phiU_baseChange`).  Hence, by the universal property of the tensor product of algebras,
there is a canonical ring map

`sectionBaseChange : Γ(X,U) ⊗[A] A' ⟶ Γ(X_{A'}, U_{A'})`,

the *base change comparison map*.  The content of affine base change is that this map is
bijective when `U` is affine (and, for the Čech comparison, that it is natural in `U`).
This file defines the map; the two properties are `sectionBaseChange_bijective` and
`sectionBaseChange_naturality` in the companion files.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

universe u

namespace Work.DSG4a

/-- The canonical **base change comparison map** `Γ(X,U) ⊗[A] A' ⟶ Γ(X_{A'}, U_{A'})`, sending
`a ⊗ b` to the product of the pullback of `a` and the structure section of `b`. -/
noncomputable def sectionBaseChange {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) :
    letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
    letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
      (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (baseChangeOpen (A := A) (A' := A') X f U)).toAlgebra
    letI : Algebra A Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
      ((DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (baseChangeOpen (A := A) (A' := A') X f U)).comp (algebraMap A A')).toAlgebra
    TensorProduct A Γ(X, U) A' →+*
      Γ(baseChangeScheme (A := A) (A' := A') X f, baseChangeOpen (A := A) (A' := A') X f U) := by
  let X' := baseChangeScheme (A := A) (A' := A') X f
  let fst := baseChangeFst (A := A) (A' := A') X f
  let snd := baseChangeSnd (A := A) (A' := A') X f
  let U' := baseChangeOpen (A := A) (A' := A') X f U
  letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  letI : Algebra A' Γ(X', U') := (DSMap.phiU A' X' snd U').toAlgebra
  letI : Algebra A Γ(X', U') := ((DSMap.phiU A' X' snd U').comp (algebraMap A A')).toAlgebra
  change TensorProduct A Γ(X, U) A' →+* Γ(X', U')
  exact (Algebra.TensorProduct.lift (R := A) (S := A)
    { toRingHom := (fst.app U).hom
      commutes' := by
        intro a
        exact phiU_baseChange (A := A) (A' := A') X f U a }
    { toRingHom := DSMap.phiU A' X' snd U'
      commutes' := by intro a; rfl }
    (fun x y => mul_comm _ _)).toRingHom

end Work.DSG4a

namespace Work.DSG4a

/-- The comparison map on a pure tensor. -/
theorem sectionBaseChange_tmul {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens)
    (a : Γ(X, U)) (b : A') :
    (letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
     sectionBaseChange (A' := A') X f U (TensorProduct.mk A Γ(X, U) A' a b)) =
      ((baseChangeFst (A := A) (A' := A') X f).app U).hom a *
        DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
          (baseChangeSnd (A := A) (A' := A') X f)
          (baseChangeOpen (A := A) (A' := A') X f U) b := by
  letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
    (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)
      (baseChangeOpen (A := A) (A' := A') X f U)).toAlgebra
  letI : Algebra A Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
    ((DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)
      (baseChangeOpen (A := A) (A' := A') X f U)).comp (algebraMap A A')).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ a b

end Work.DSG4a

namespace Work.DSG4a

/-- The statement of **affine base change**: for an affine open `U ⊆ X`, the comparison map
`Γ(X,U) ⊗[A] A' → Γ(X_{A'}, U_{A'})` is bijective. -/
noncomputable def IsBaseChangeIso {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens) : Prop :=
  letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
    (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)
      (baseChangeOpen (A := A) (A' := A') X f U)).toAlgebra
  letI : Algebra A Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f U) :=
    ((DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)
      (baseChangeOpen (A := A) (A' := A') X f U)).comp (algebraMap A A')).toAlgebra
  Function.Bijective (sectionBaseChange (A := A) (A' := A') X f U)

end Work.DSG4a

namespace Work.DSG4a

/-- The pure tensor `a ⊗[A] b` in `Γ(X,U) ⊗[A] A'`, where the `A`-module structure on
`Γ(X,U)` is the one induced by `f : X ⟶ Spec A`. -/
noncomputable def tmulElem {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (U : X.Opens) (a : Γ(X, U)) (b : A') :
    (letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
     TensorProduct A Γ(X, U) A') :=
  letI : Algebra A Γ(X, U) := (DSMap.phiU A X f U).toAlgebra
  TensorProduct.mk A Γ(X, U) A' a b

end Work.DSG4a
