import Mathlib
import Submission.Work.DSG4a.BaseChange
import Submission.Work.DSG1.Basic

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

section PhiEq

variable {A : Type u} [CommRing A]

/-- The comparison map `DSMap.phi A X f : A → Γ(X, ⊤)` is `f.appTop` composed with the
inverse of the canonical isomorphism `Γ(Spec A, ⊤) ≅ A`. -/
lemma phiU_baseChange_phi_eq (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    DSMap.phi A X f a = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hkey : (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of A)))
      (CommRingCat.ofHom (DSMap.phi A X f)).op = f :=
    Equiv.apply_symm_apply _ _
  have h := ΓSpec_adjunction_homEquiv_eq (X := X) (B := CommRingCat.of A)
    (CommRingCat.ofHom (DSMap.phi A X f))
  rw [hkey] at h
  rw [h]
  simp

end PhiEq

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- The compatibility of `ΓSpecIso` with the morphism `Spec A' ⟶ Spec A` induced by `algebraMap`. -/
lemma phiU_baseChange_specAlgebraMap_appTop (a : A) :
    (specAlgebraMap (A := A) (A' := A')).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom (algebraMap A A' a) := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (specAlgebraMap (A := A) (A' := A')).appTop
      = CommRingCat.ofHom (algebraMap A A') ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A A'))).symm
  exact ConcreteCategory.congr_hom h a

/-- Restriction to `⊤` commutes with pulling back sections along the first projection of a
pullback square (specialisation of the naturality of `Scheme.Hom.app`). -/
lemma phiU_baseChange_nat (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens)
    (a : A) :
    ((pullback.fst f (specAlgebraMap (A := A) (A' := A'))).app U).hom
        ((X.presheaf.map (homOfLE le_top).op).hom (DSMap.phi A X f a)) =
      ((pullback f (specAlgebraMap (A := A) (A' := A'))).presheaf.map
          (homOfLE le_top).op).hom
        (((pullback.fst f (specAlgebraMap (A := A) (A' := A'))).app ⊤).hom
          (DSMap.phi A X f a)) := by
  have hn := Scheme.Hom.naturality (f := pullback.fst f (specAlgebraMap (A := A) (A' := A')))
    (i := (homOfLE le_top : U ⟶ ⊤).op)
  have h2 := ConcreteCategory.congr_hom hn (DSMap.phi A X f a)
  simp only [CategoryTheory.comp_apply] at h2
  exact h2

/-- The comparison of the top sections along the pullback square, i.e. the compatibility of
`phi` with the base change `Spec A' ⟶ Spec A`. -/
lemma phiU_baseChange_top (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    ((pullback.fst f (specAlgebraMap (A := A) (A' := A'))).app ⊤).hom (DSMap.phi A X f a) =
      DSMap.phi A' (pullback f (specAlgebraMap (A := A) (A' := A')))
        (pullback.snd f (specAlgebraMap (A := A) (A' := A'))) (algebraMap A A' a) := by
  have hA : ((pullback.fst f (specAlgebraMap (A := A) (A' := A'))).app ⊤).hom
      (DSMap.phi A X f a) =
      ((pullback.fst f (specAlgebraMap (A := A) (A' := A'))).app ⊤).hom
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := by
    rw [phiU_baseChange_phi_eq]
  have hB : DSMap.phi A' (pullback f (specAlgebraMap (A := A) (A' := A')))
        (pullback.snd f (specAlgebraMap (A := A) (A' := A'))) (algebraMap A A' a) =
      (Scheme.Hom.appTop (pullback.snd f (specAlgebraMap (A := A) (A' := A')))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom (algebraMap A A' a)) := by
    rw [phiU_baseChange_phi_eq]
  have h1 : ((pullback.fst f (specAlgebraMap (A := A) (A' := A'))).app ⊤).hom
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) =
      ((pullback.fst f (specAlgebraMap (A := A) (A' := A'))) ≫ f).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  have h2 : ((pullback.snd f (specAlgebraMap (A := A) (A' := A'))) ≫
        (specAlgebraMap (A := A) (A' := A'))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.Hom.appTop (pullback.snd f (specAlgebraMap (A := A) (A' := A')))).hom
        ((specAlgebraMap (A := A) (A' := A')).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [hA, hB, h1, pullback.condition, h2, phiU_baseChange_specAlgebraMap_appTop]

theorem phiU_baseChange {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (U : X.Opens) (a : A) :
    ((AlgebraicGeometry.Scheme.Hom.app (Work.DSG4a.baseChangeFst (A := A) (A' := A') X f) U).hom)
        (DSMap.phiU A X f U a) =
      DSMap.phiU A' (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f)
        (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f)
        (Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f U)
        (algebraMap A A' a) := by
  simp only [DSMap.phiU, RingHom.comp_apply]
  rw [phiU_baseChange_nat X f U a, phiU_baseChange_top X f a]

end Work.DSG4a
