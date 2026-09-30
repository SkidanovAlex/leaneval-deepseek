/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary definitions for the affine piece of the relative quotient (area SY, `relQuot`)

This file provides the vocabulary used to reduce the affine piece of the relative quotient
property to a statement about affine schemes:

* `Work.SymQuot.RelQuot.instAlgebraSections` — the `K`-algebra structure on the sections
  `Γ(X, U)` of a `K`-scheme `X`, induced by the structure morphism `X ⟶ Spec K`;
* `specMap_algebraMap_sections` — the structure morphism of the affine open `Spec Γ(X,U)` is
  `Spec.map (algebraMap K Γ(X,U))`;
* `mkIsoSpecOf` — the identification of the affine open subscheme `U ⊆ X` (as a `K`-scheme
  `Over.mk (U.ι ≫ X.hom)`) with `specOf Γ(X,U)`;
* `specTensorIso` — the identification `specOf A ⊗ specOf B ≅ specOf (A ⊗[K] B)` of a product of
  affine `K`-schemes with the spectrum of the tensor product of the rings.
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.RelQuot.tensorIncl_range
import Submission.Work.SymQuot.RelQuot.specFixedPoints_lift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical MonoidalCategory

universe u

namespace Work.SymQuot.RelQuot

variable {K : Type u} [Field K]

/-- **The `K`-algebra structure on the sections `Γ(X, U)` of a `K`-scheme `X`**, induced by the
structure morphism `X.hom : X ⟶ Spec K` and the canonical identification `Γ(Spec K) ≅ K`. -/
noncomputable instance instAlgebraSections (X : Work.SpecLin.Sch K) (U : X.left.Opens) :
    Algebra K Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appLE ⊤ U le_top).hom.toAlgebra

/-- **The structure morphism of an affine open subscheme.**  For an affine open `U ⊆ X` of a
`K`-scheme `X`, the composite `Spec Γ(X,U) ⟶ U ⟶ X ⟶ Spec K` is
`Spec.map (algebraMap K Γ(X,U))`. -/
theorem specMap_algebraMap_sections (X : Work.SpecLin.Sch K) (U : X.left.Opens)
    (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, U))) = hU.fromSpec ≫ X.hom := by
  have key : Spec.map (X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv = hU.fromSpec ≫ X.hom := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (f := X.hom)
      (U := (⊤ : (Spec (CommRingCat.of K)).Opens)) (V := U)
      (isAffineOpen_top (Spec (CommRingCat.of K))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rwa [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← key, ← Spec.map_comp]
  rw [show (CommRingCat.ofHom (algebraMap K Γ(X.left, U))) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤) from rfl]

/-- **An affine open subscheme of a `K`-scheme, as a `K`-scheme**, is the spectrum of its ring of
sections.  Here `U ⊆ X.left` is any affine open; the `K`-scheme is `Over.mk (U.ι ≫ X.hom)`. -/
noncomputable def mkIsoSpecOf (X : Work.SpecLin.Sch K) (U : X.left.Opens)
    (hU : IsAffineOpen U) :
    Over.mk (U.ι ≫ X.hom) ≅ Work.SpecLin.specOf (K := K) Γ(X.left, U) :=
  Over.isoMk (f := Over.mk (U.ι ≫ X.hom))
    (g := Work.SpecLin.specOf (K := K) Γ(X.left, U))
    (hl := hU.isoSpec) (hw := by
      show hU.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, U))) = U.ι ≫ X.hom
      rw [IsAffineOpen.isoSpec_hom hU, specMap_algebraMap_sections X U hU,
        ← Category.assoc, IsAffineOpen.toSpecΓ_fromSpec hU])

@[simp]
lemma mkIsoSpecOf_hom_left (X : Work.SpecLin.Sch K) (U : X.left.Opens) (hU : IsAffineOpen U) :
    (mkIsoSpecOf X U hU).hom.left = U.toSpecΓ := rfl

/-- The inverse of `mkIsoSpecOf` on underlying schemes. -/
lemma mkIsoSpecOf_inv_left (X : Work.SpecLin.Sch K) (U : X.left.Opens) (hU : IsAffineOpen U) :
    (mkIsoSpecOf X U hU).inv.left = hU.isoSpec.inv :=
  Over.isoMk_inv_left _ _

/-- **The product of two affine `K`-schemes is the spectrum of the tensor product.** -/
noncomputable def specTensorIso (A B : Type u) [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] :
    Work.SpecLin.specOf (K := K) A ⊗ Work.SpecLin.specOf (K := K) B ≅
      Work.SpecLin.specOf (K := K) (A ⊗[K] B) :=
  Over.isoMk (f := Work.SpecLin.specOf (K := K) A ⊗ Work.SpecLin.specOf (K := K) B)
    (g := Work.SpecLin.specOf (K := K) (A ⊗[K] B))
    (hl := AlgebraicGeometry.pullbackSpecIso K A B) (hw := by
      show (AlgebraicGeometry.pullbackSpecIso K A B).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B))) =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K A)))
          (Spec.map (CommRingCat.ofHom (algebraMap K B))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K A))
      rw [show (algebraMap K (A ⊗[K] B)) =
          (algebraMap A (A ⊗[K] B)).comp (algebraMap K A) from
          IsScalarTower.algebraMap_eq K A (A ⊗[K] B)]
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
        AlgebraicGeometry.pullbackSpecIso_hom_fst'])

@[simp]
lemma specTensorIso_hom_left (A B : Type u) [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] :
    (specTensorIso (K := K) A B).hom.left = (AlgebraicGeometry.pullbackSpecIso K A B).hom :=
  rfl

@[simp]
lemma specTensorIso_inv_left (A B : Type u) [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] :
    (specTensorIso (K := K) A B).inv.left = (AlgebraicGeometry.pullbackSpecIso K A B).inv :=
  Over.isoMk_inv_left _ _


section ChartRing

variable {Γ : Type u} [Group Γ]

/-- **The action on the sections of an invariant open is by `K`-algebra maps.**  If the action of
`Γ` on a `K`-scheme `X` is by morphisms over `Spec K` (`hs`), then the pullback of sections along
`A.hom g` fixes the image of `K` in `Γ(X, U)`. -/
lemma sectionHom_algebraMap (X : Work.SpecLin.Sch K) (A : Work.SymQuot.GAction Γ X.left)
    {U : X.left.Opens} (hU : A.IsInvariantOpen U)
    (hs : ∀ g : Γ, A.hom g ≫ X.hom = X.hom) (g : Γ) (k : K) :
    Work.SymQuot.GAction.sectionHom A U hU g (algebraMap K Γ(X.left, U) k) =
      algebraMap K Γ(X.left, U) k := by
  have hkey : (algebraMap K Γ(X.left, U)) =
      (Scheme.Hom.appLE (X.hom) ⊤ U le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
    rw [RingHom.algebraMap_toAlgebra]
    ext x
    rfl
  rw [hkey, RingHom.comp_apply]
  rw [Work.SymQuot.GAction.sectionHom_apply]
  rw [← ConcreteCategory.comp_apply]
  rw [show (Scheme.Hom.appLE (X.hom) ⊤ U le_top ≫ Scheme.Hom.appLE (A.hom g) U U
        (le_of_eq (hU g).symm))
      = Scheme.Hom.appLE (A.hom g ≫ X.hom) ⊤ U le_top from
    Scheme.Hom.appLE_comp_appLE (A.hom g) X.hom ⊤ U U le_top (le_of_eq (hU g).symm)]
  rw [Work.SymQuot.appLE_congr_hom (hs g)
    ((le_top : U ≤ ⊤).trans (le_of_eq (Scheme.Hom.preimage_top (A.hom g ≫ X.hom)).symm)) le_top]

/-- **The `Γ`-action on the sections over an invariant open commutes with the `K`-algebra
structure** (the action being by `K`-algebra automorphisms). -/
theorem smulCommClassSections (X : Work.SpecLin.Sch K)
    (A : Work.SymQuot.GAction Γ X.left) {U : X.left.Opens} (hU : A.IsInvariantOpen U)
    (hs : ∀ g : Γ, A.hom g ≫ X.hom = X.hom) :
    letI : MulSemiringAction Γ ↥Γ(X.left, U) := A.sectionMulSemiringAction U hU
    SMulCommClass Γ K ↥Γ(X.left, U) :=
  letI : MulSemiringAction Γ ↥Γ(X.left, U) := A.sectionMulSemiringAction U hU
  ⟨fun g k x => by
    show Work.SymQuot.GAction.sectionHom A U hU g⁻¹ (algebraMap K ↥Γ(X.left, U) k * x) =
      algebraMap K ↥Γ(X.left, U) k * Work.SymQuot.GAction.sectionHom A U hU g⁻¹ x
    rw [map_mul, sectionHom_algebraMap X A hU hs g⁻¹ k]⟩

end ChartRing

section Monoidal

/-- **Conjugation of an endomorphism by an isomorphism**, tensored with an identity. -/
lemma tensorHom_conj {C : Type*} [Category C] [MonoidalCategory C] {A A' B B' : C}
    (u : A ≅ A') (v : B ≅ B') (a : A ⟶ A) :
    (a ⊗ₘ 𝟙 B) ≫ (u.hom ⊗ₘ v.hom) = (u.hom ⊗ₘ v.hom) ≫ ((u.inv ≫ a ≫ u.hom) ⊗ₘ 𝟙 B') := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc]

/-- **Conjugation of a morphism by an isomorphism**, tensored with an identity. -/
lemma tensorHom_conjIso {C : Type*} [Category C] [MonoidalCategory C] {P Q R R' S S' : C}
    (gm : P ⟶ Q) (c : Q ≅ R) (u : P ≅ R') (a : R' ⟶ R) (v : S ≅ S')
    (hgm : gm ≫ c.hom = u.hom ≫ a) :
    (gm ⊗ₘ 𝟙 S) ≫ (c.hom ⊗ₘ v.hom) = (u.hom ⊗ₘ v.hom) ≫ (a ⊗ₘ 𝟙 S') := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, hgm]

end Monoidal


section ChartU

variable {Γ : Type u} [Group Γ] [Fintype Γ] {X Y : Work.SpecLin.Sch K}

/-- Restriction of sections along `V ≤ f ⁻¹ᵁ U`, composed with the open immersion `U.ι`. -/
private lemma resLE_comp_ι_assoc' {X Y Z : Scheme} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (g : Y ⟶ Z) :
    Scheme.Hom.resLE f U V e ≫ U.ι ≫ g = V.ι ≫ f ≫ g := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- **The chart of a chart of the quotient data is affine over `K` through the invariants of the
sections.**  The structure morphism of the chart `Spec Γ(X,U)^Γ` of the quotient `X/Γ` is
`Spec.map (algebraMap K Γ(X,U)^Γ)`, for the `K`-algebra structure on the invariants induced by
the structure morphism of the quotient (equivalently, by the restriction of the `K`-algebra
structure on `Γ(X,U)`; the two agree because the action is over `Spec K`). -/
theorem chartU_hom_eq_algebraMap (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
    letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
    (chartU D hbase U).hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap K ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ))) := by
  letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
  letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
  set hU : Spec (CommRingCat.of ↥Γ(X.left, U.1)) ⟶ Spec (CommRingCat.of K) :=
    U.2.1.isoSpec.inv ≫ (U.1.ι ≫ X.hom) with hU_def
  have hinv : ∀ g : Γ,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ ↥Γ(X.left, U.1) g)) ≫ hU
        = hU := by
    intro g
    rw [hU_def, Work.SymQuot.Chart.toRingHom_eq_sectionHom D.action U.2.2 g,
      Work.SymQuot.Chart.spec_map_sectionHom D.action U.2.1 U.2.2 g]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc,
      resLE_comp_ι_assoc' (D.action.hom g⁻¹) (le_of_eq (U.2.2 g⁻¹).symm) X.hom, hbase g⁻¹]
  obtain ⟨gU, hgU, huniq⟩ :=
    Work.SymQuot.Chart.existsUnique_affine_target (G := Γ) hU hinv
  have hchart : Spec.map (CommRingCat.ofHom (Subring.subtype
        (FixedPoints.subring ↥Γ(X.left, U.1) Γ))) ≫
      (D.chartι U ≫ D.quotientHom X.hom hbase) = hU := by
    have h1 : (U.2.1.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Subring.subtype (FixedPoints.subring ↥Γ(X.left, U.1) Γ)))) ≫
        (D.chartι U ≫ D.quotientHom X.hom hbase) = U.1.ι ≫ X.hom := by
      rw [IsAffineOpen.isoSpec_hom U.2.1, ← Work.SymQuot.GAction.chartMap, ← Category.assoc,
        ← D.quotientMap_chartι U, Category.assoc, D.quotientMap_quotientHom X.hom hbase]
    rw [hU_def, ← h1]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
  have hmine : Spec.map (CommRingCat.ofHom (Subring.subtype
        (FixedPoints.subring ↥Γ(X.left, U.1) Γ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K
        ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ))) = hU := by
    have hcomp : (CommRingCat.ofHom (algebraMap K
          ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ)) :
          CommRingCat.of K ⟶ CommRingCat.of ↥(FixedPoints.subring ↥Γ(X.left, U.1) Γ)) ≫
        (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring ↥Γ(X.left, U.1) Γ)) :
          CommRingCat.of ↥(FixedPoints.subring ↥Γ(X.left, U.1) Γ) ⟶
            CommRingCat.of ↥Γ(X.left, U.1)) =
        CommRingCat.ofHom (algebraMap K ↥Γ(X.left, U.1)) :=
      (CommRingCat.ofHom_comp (algebraMap K ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ))
        (Subring.subtype (FixedPoints.subring ↥Γ(X.left, U.1) Γ))).trans (by congr 1)
    have h2 : Spec.map (CommRingCat.ofHom (Subring.subtype
          (FixedPoints.subring ↥Γ(X.left, U.1) Γ))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K
          ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ))) =
        Spec.map (CommRingCat.ofHom (algebraMap K ↥Γ(X.left, U.1))) := by
      refine (Spec.map_comp
        (CommRingCat.ofHom (algebraMap K ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ)) :
          CommRingCat.of K ⟶ CommRingCat.of ↥(FixedPoints.subring ↥Γ(X.left, U.1) Γ))
        (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring ↥Γ(X.left, U.1) Γ)) :
          CommRingCat.of ↥(FixedPoints.subring ↥Γ(X.left, U.1) Γ) ⟶
            CommRingCat.of ↥Γ(X.left, U.1))).symm.trans ?_
      rw [hcomp]
    rw [h2, specMap_algebraMap_sections X U.1 U.2.1, hU_def]
    simp only [IsAffineOpen.fromSpec, Category.assoc]
  rw [chartU_hom, relQuotScheme_hom]
  exact (huniq _ hchart).trans (huniq _ hmine).symm

/-- A variant of `mkIsoSpecOf` whose source is phrased as `ovU U`. -/
noncomputable def ovUIsoSpecOf (D : Work.SymQuot.QuotientData Γ X.left) (U : D.Chart) :
    ovU (D := D) U ≅ Work.SpecLin.specOf (K := K) ↥Γ(X.left, U.1) :=
  mkIsoSpecOf X U.1 U.2.1

@[simp]
lemma ovUIsoSpecOf_hom_left (D : Work.SymQuot.QuotientData Γ X.left) (U : D.Chart) :
    (ovUIsoSpecOf D U).hom.left = U.1.toSpecΓ := rfl

@[simp]
lemma ovUIsoSpecOf_inv_left (D : Work.SymQuot.QuotientData Γ X.left) (U : D.Chart) :
    (ovUIsoSpecOf D U).inv.left = U.2.1.isoSpec.inv :=
  mkIsoSpecOf_inv_left X U.1 U.2.1

/-- **The chart of a chart, as a `K`-scheme, is the spectrum of the ring of invariants.** -/
noncomputable def chartIsoSpecOf (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
    letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
    chartU D hbase U ≅
      Work.SpecLin.specOf (K := K) ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ) :=
  letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
  letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
  Over.isoMk (f := chartU D hbase U)
    (g := Work.SpecLin.specOf (K := K) ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ))
    (hl := Iso.refl _) (hw := by
      show Spec.map (CommRingCat.ofHom (algebraMap K
          ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ))) = (chartU D hbase U).hom
      exact (chartU_hom_eq_algebraMap D hbase U).symm)

@[simp]
lemma chartIsoSpecOf_hom_left (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
    letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
    (chartIsoSpecOf D hbase U).hom.left = 𝟙 (D.chart U) :=
  Over.isoMk_hom_left _ _

/-- **The quotient map on the affine piece `U`** -/
theorem chartIsoSpecOf_chartMapOv (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
    letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
    (ovUIsoSpecOf D U).inv ≫ chartMapOv D hbase U ≫ (chartIsoSpecOf D hbase U).hom
      = Work.SpecLin.specOfMap (FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ).val := by
  letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
  letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
  apply Over.OverMorphism.ext
  show U.2.1.isoSpec.inv ≫ (U.1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Subring.subtype
        (FixedPoints.subring ↥Γ(X.left, U.1) Γ)))) ≫ 𝟙 (D.chart U)
      = Spec.map (CommRingCat.ofHom ((Subalgebra.val
          (FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ)).toRingHom))
  rw [Category.comp_id, ← Category.assoc, ← IsAffineOpen.isoSpec_hom U.2.1,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- **The action of `Γ` on the affine piece `U`** -/
theorem ovUIsoSpecOf_actU (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (g : Γ) :
    letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
    letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
    (ovUIsoSpecOf D U).inv ≫ actU D hbase U g ≫ (ovUIsoSpecOf D U).hom
      = Work.SpecLin.specOfMap (MulSemiringAction.toAlgHom K ↥Γ(X.left, U.1) g⁻¹) := by
  letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
  letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
  apply Over.OverMorphism.ext
  show U.2.1.isoSpec.inv ≫
        (D.action.hom g).resLE U.1 U.1 (le_of_eq (U.2.2 g).symm) ≫ U.1.toSpecΓ
      = Spec.map (CommRingCat.ofHom
          ((MulSemiringAction.toAlgHom K ↥Γ(X.left, U.1) g⁻¹).toRingHom))
  rw [← Work.SymQuot.Chart.toSpecΓ_sectionHom D.action U.2.2 g, ← IsAffineOpen.isoSpec_hom U.2.1,
    Iso.inv_hom_id_assoc]
  congr 1
  ext x
  show D.action.sectionHom U.1 U.2.2 g x =
    MulSemiringAction.toRingHom Γ ↥Γ(X.left, U.1) g⁻¹ x
  rw [Work.SymQuot.Chart.toRingHom_eq_sectionHom D.action U.2.2 g⁻¹]
  simp only [inv_inv]


/-- A variant of `mkIsoSpecOf` whose source is phrased as `ovV V`. -/
noncomputable def ovVIsoSpecOf (V : Y.left.affineOpens) :
    ovV (Y := Y) V ≅ Work.SpecLin.specOf (K := K) ↥Γ(Y.left, V.1) :=
  mkIsoSpecOf Y V.1 V.2

@[simp]
lemma ovVIsoSpecOf_hom_left (V : Y.left.affineOpens) :
    (ovVIsoSpecOf (K := K) V).hom.left = V.1.toSpecΓ := rfl

@[simp]
lemma ovVIsoSpecOf_inv_left (V : Y.left.affineOpens) :
    (ovVIsoSpecOf (K := K) V).inv.left = V.2.isoSpec.inv :=
  mkIsoSpecOf_inv_left Y V.1 V.2

end ChartU

end Work.SymQuot.RelQuot
