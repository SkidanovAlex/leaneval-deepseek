import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSG1.Basic
import Submission.Work.DSG1.Setup

/-!
# DSG1: bookkeeping lemmas for the unit compatibility of `Work.DSG1.comparison`

This file collects the small structural lemmas used in the proof of the unit compatibility
in `Submission/Work/DSG1/comparison.lean`:

* `Work.DSG1.linMap`: the structure map `A ⟶ Γ(X, 𝒪_X)` as an `A`-linear map (the first factor
  of `DSMap.rgUnit`), together with `Work.DSG1.rgUnit_eq` which rewrites `DSMap.rgUnit` in
  terms of it;
* `Work.DSG1.linMap_comp_pushforwardUnit`: the compatibility (`Work.DSG1.phi_comp`) of the
  `A`-module structures: `lin_X ≫ g_*(σ) = lin_{X'}`.
-/

namespace Work.DSG1

open CategoryTheory AlgebraicGeometry Limits

universe a

/-- The structure map `A ⟶ Γ(X,𝒪_X)` as a morphism of `A`-modules (the first factor of
`DSMap.rgUnit`). -/
noncomputable def linMap (A : Type a) [CommRing A] {X : Scheme.{a}} (f : X ⟶ Spec (.of A)) :
    (letI : Algebra A Γ(X, ⊤) := (DSMap.phi A X f).toAlgebra
     ModuleCat.of A A ⟶ ModuleCat.of A Γ(X, ⊤)) :=
  letI : Algebra A Γ(X, ⊤) := (DSMap.phi A X f).toAlgebra
  ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))

/-- `DSMap.rgUnit` is `linMap` followed by the single level unit of the derived functor. -/
lemma rgUnit_eq (A : Type a) [CommRing A] {X : Scheme.{a}} (f : X ⟶ Spec (.of A))
    [HasDerivedCategory (ModuleCat.{a} A)]
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] :
    DSMap.rgUnit A X f =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{a} A) 0).map (linMap A f) ≫
        (LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit'
          (DSMap.GammaA A X f) 0).app (SheafOfModules.unit X.ringCatSheaf) := rfl

/-- The structure map `𝒪_X ⟶ g_* 𝒪_{X'}` intertwines the two `A`-linear structure maps on
global sections (`Work.DSG1.phi_comp`): `lin_X ≫ Γ(g)(σ) = lin_{X'}`. -/
lemma linMap_comp_pushforwardUnit (A : Type a) [CommRing A] {X X' : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) (g : X' ⟶ X) :
    linMap A f ≫ (DSMap.GammaA A X f).map
        (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
      = linMap A (g ≫ f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change (ConcreteCategory.hom ((DSMap.GammaA A X f).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom))) ((DSMap.phi A X f) b)
    = (DSMap.phi A X' (g ≫ f)) b
  rw [phi_comp (A := A) f g]
  rfl

section Assoc

/-- `((f ≫ g) ≫ h) ≫ k = f ≫ g ≫ h ≫ k`. -/
lemma reassoc4 {C : Type*} [Category* C] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (k : d ⟶ e) : ((f ≫ g) ≫ h) ≫ k = f ≫ g ≫ h ≫ k := by
  simp only [Category.assoc]

/-- `((p ≫ q ≫ r) ≫ (s ≫ t)) = p ≫ q ≫ r ≫ s ≫ t`. -/
lemma reassoc5 {C : Type*} [Category* C] {a b c d e f : C} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d)
    (s : d ⟶ e) (t : e ⟶ f) : ((p ≫ q ≫ r) ≫ (s ≫ t)) = p ≫ q ≫ r ≫ s ≫ t := by
  simp only [Category.assoc]

/-- `f ≫ g ≫ h = (f ≫ g) ≫ h`. -/
lemma assoc_swap {C : Type*} [Category* C] {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    f ≫ g ≫ h = (f ≫ g) ≫ h :=
  (Category.assoc f g h).symm

/-- `(f ≫ g ≫ h) ≫ k = f ≫ (g ≫ (h ≫ k))`. -/
lemma reassoc4' {C : Type*} [Category* C] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (k : d ⟶ e) : (f ≫ g ≫ h) ≫ k = f ≫ g ≫ h ≫ k := by
  simp only [Category.assoc]

end Assoc

/-- `((f ≫ (g ≫ (h ≫ k))) ≫ w) = f ≫ g ≫ h ≫ k ≫ w`. -/
lemma push_out4 {C : Type*} [Category* C] {a b c d e z : C} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (k : d ⟶ e) (w : e ⟶ z) : ((f ≫ (g ≫ (h ≫ k))) ≫ w) = f ≫ g ≫ h ≫ k ≫ w := by
  simp only [Category.assoc]

/-- `(f ≫ g) ≫ (h ≫ k) = f ≫ g ≫ h ≫ k`. -/
lemma reassoc_pair_pair {C : Type*} [Category* C] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (k : d ⟶ e) : (f ≫ g) ≫ (h ≫ k) = f ≫ g ≫ h ≫ k := by
  simp only [Category.assoc]

/-- `f ≫ (g ≫ (h ≫ k)) = ((f ≫ g) ≫ h) ≫ k`. -/
lemma pull_in4 {C : Type*} [Category* C] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (k : d ⟶ e) : f ≫ g ≫ h ≫ k = ((f ≫ g) ≫ h) ≫ k := by
  simp only [Category.assoc]

/-- `F.map e.inv ≫ F.map e.hom ≫ w = w`. -/
lemma map_cancel {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D) {a b : C}
    (e : a ≅ b) {c : D} (w : F.obj b ⟶ c) : F.map e.inv ≫ F.map e.hom ≫ w = w := by
  rw [← Functor.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

/-- `e.inv ≫ e.hom ≫ w = w`. -/
lemma iso_cancel {C : Type*} [Category* C] {a b c : C} (e : a ≅ b) (w : b ⟶ c) :
    e.inv ≫ e.hom ≫ w = w := by
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- `f ≫ inv f ≫ w = w`. -/
lemma cancel_hom_inv {C : Type*} [Category* C] {a b c : C} (f : a ⟶ b) [IsIso f] (w : a ⟶ c) :
    f ≫ inv f ≫ w = w :=
  IsIso.hom_inv_id_assoc f w

end Work.DSG1
