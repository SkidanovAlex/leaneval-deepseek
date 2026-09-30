/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vocabulary for the relative quotient property (area SY, `relQuot`)

The relative quotient property `Work.SymQuot.RelQuot.relQuot` says that for a `K`-scheme `X` with
an action of a finite group `Γ` by `K`-automorphisms, a quotient `X/Γ` and any `K`-scheme `Y`,
the quotient of `X ⊗ Y` by the induced action of `Γ` (acting on the first factor) is
`(X/Γ) ⊗ Y`, with quotient map `q ▷ Y`.

The *local* (affine) input is the following algebra: for a `K`-algebra `A` with a `Γ`-action by
`K`-algebra automorphisms and any `K`-algebra `R`, the fixed points of the induced action of `Γ`
on `A ⊗[K] R` (acting on the first factor) are the image of `A^Γ ⊗[K] R` — this is
`Work.SymQuot.Invariants.tensor_fixedPoints_of_flat`, `K` being a field.

This file collects the definitions used to state and prove that:

* `Work.SymQuot.RelQuot.tensorAct` — the `Γ`-action on `A ⊗[K] R` through the first factor, and
  the `MulSemiringAction`/`SMulCommClass` instances making it available;
* `Work.SymQuot.RelQuot.tensorIncl` — the canonical map `A^Γ ⊗[K] R ⟶ A ⊗[K] R`;
* `Work.SymQuot.RelQuot.gActionOfRingAction` — the action on `Spec C` induced by a
  `MulSemiringAction` on the ring `C`.
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.Setup

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
open scoped Classical TensorProduct

universe u

namespace Work.SymQuot.RelQuot

variable {K : Type u} [Field K]

section TensorAction

variable {Γ : Type u} [Group Γ]

/-- **The action of `g : Γ` on `A ⊗[K] R` through the first factor**: the `K`-algebra
automorphism induced by `g : A →ₐ[K] A` and the identity on `R`. -/
noncomputable def tensorAct (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A]
    [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] (g : Γ) :
    A ⊗[K] R →ₐ[K] A ⊗[K] R :=
  Algebra.TensorProduct.map (MulSemiringAction.toAlgHom K A g) (AlgHom.id K R)

@[simp]
lemma tensorAct_tmul (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A]
    [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] (g : Γ) (a : A) (r : R) :
    tensorAct A R g (a ⊗ₜ[K] r) = (g • a) ⊗ₜ[K] r := by
  simp [tensorAct]

lemma tensorAct_one_apply (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A]
    [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] (x : A ⊗[K] R) :
    tensorAct A R (1 : Γ) x = x := by
  have h1 : MulSemiringAction.toAlgHom K A (1 : Γ) = AlgHom.id K A := by
    refine AlgHom.ext fun a => ?_
    rw [MulSemiringAction.toAlgHom_apply, one_smul]
    rfl
  rw [tensorAct, h1, Algebra.TensorProduct.map_id]
  rfl

lemma tensorAct_mul_apply (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A]
    [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] (g h : Γ) (x : A ⊗[K] R) :
    tensorAct A R (g * h) x = tensorAct A R g (tensorAct A R h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [tensorAct_tmul, tensorAct_tmul, tensorAct_tmul, mul_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable instance instMulSemiringActionTensor (A : Type u) [CommRing A] [Algebra K A]
    [MulSemiringAction Γ A] [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] :
    MulSemiringAction Γ (A ⊗[K] R) where
  smul g x := tensorAct A R g x
  one_smul x := tensorAct_one_apply A R x
  mul_smul g h x := tensorAct_mul_apply A R g h x
  smul_zero g := map_zero (tensorAct A R g)
  smul_add g x y := map_add (tensorAct A R g) x y
  smul_mul g x y := map_mul (tensorAct A R g) x y
  smul_one g := map_one (tensorAct A R g)

instance instSMulCommClassTensor (A : Type u) [CommRing A] [Algebra K A]
    [MulSemiringAction Γ A] [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] :
    SMulCommClass Γ K (A ⊗[K] R) where
  smul_comm g k x := by
    change tensorAct A R g (k • x) = k • tensorAct A R g x
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]

/-- **The canonical map `A^Γ ⊗[K] R ⟶ A ⊗[K] R`.** -/
noncomputable def tensorIncl (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A]
    [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R] :
    ↥(FixedPoints.subalgebra K A Γ) ⊗[K] R →ₐ[K] A ⊗[K] R :=
  Algebra.TensorProduct.map (FixedPoints.subalgebra K A Γ).val (AlgHom.id K R)

@[simp]
lemma tensorIncl_tmul (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A]
    [SMulCommClass Γ K A] (R : Type u) [CommRing R] [Algebra K R]
    (a : ↥(FixedPoints.subalgebra K A Γ)) (r : R) :
    tensorIncl A R (a ⊗ₜ[K] r) = (a : A) ⊗ₜ[K] r := by
  simp [tensorIncl]

end TensorAction

section GActionOfRing

variable {Γ : Type u} [Group Γ]

/-- **The action on `Spec C` induced by a `MulSemiringAction` of `Γ` on a ring `C`.**

With the convention `g • 𝔭 = hom g 𝔭 = Spec.map (ofHom (toRingHom g⁻¹)) 𝔭` the *sections* action
`Work.SymQuot.GAction.sectionMulSemiringAction` on `Γ(Spec C, ⊤)` recovers
`MulSemiringAction.toRingHom Γ C`, via `Scheme.ΓSpecIso`. -/
noncomputable def gActionOfRingAction (C : Type u) [CommRing C] [MulSemiringAction Γ C] :
    Work.SymQuot.GAction Γ (Spec (CommRingCat.of C)) where
  hom g := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g⁻¹))
  inv g := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g))
  hom_inv g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcomp : (MulSemiringAction.toRingHom Γ C g⁻¹).comp (MulSemiringAction.toRingHom Γ C g)
        = RingHom.id C := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, RingHom.id_apply, MulSemiringAction.toRingHom_apply,
        MulSemiringAction.toRingHom_apply, ← mul_smul, inv_mul_cancel, one_smul]
    rw [hcomp, show CommRingCat.ofHom (RingHom.id C) = 𝟙 (CommRingCat.of C) from rfl, Spec.map_id]
  inv_hom g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcomp : (MulSemiringAction.toRingHom Γ C g).comp (MulSemiringAction.toRingHom Γ C g⁻¹)
        = RingHom.id C := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, RingHom.id_apply, MulSemiringAction.toRingHom_apply,
        MulSemiringAction.toRingHom_apply, ← mul_smul, mul_inv_cancel, one_smul]
    rw [hcomp, show CommRingCat.ofHom (RingHom.id C) = 𝟙 (CommRingCat.of C) from rfl, Spec.map_id]
  hom_one := by
    have h1 : MulSemiringAction.toRingHom Γ C (1 : Γ) = RingHom.id C := by
      refine RingHom.ext fun c => ?_
      rw [RingHom.id_apply, MulSemiringAction.toRingHom_apply, one_smul]
    show Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C (1 : Γ)⁻¹)) =
      𝟙 (Spec (CommRingCat.of C))
    rw [show ((1 : Γ)⁻¹) = 1 from inv_one, h1,
      show CommRingCat.ofHom (RingHom.id C) = 𝟙 (CommRingCat.of C) from rfl, Spec.map_id]
  hom_mul g h := by
    show Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C (g * h)⁻¹)) =
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C h⁻¹)) ≫
        Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g⁻¹))
    rw [← Spec.map_comp (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C g⁻¹))
      (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ C h⁻¹)),
      ← CommRingCat.ofHom_comp (MulSemiringAction.toRingHom Γ C g⁻¹)
        (MulSemiringAction.toRingHom Γ C h⁻¹)]
    congr 1
    congr 1
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, MulSemiringAction.toRingHom_apply,
      MulSemiringAction.toRingHom_apply, mul_inv_rev, mul_smul]

end GActionOfRing

section Pieces

variable {Γ : Type u} [Group Γ] [Fintype Γ] {X Y : Work.SpecLin.Sch K}

/-- The chart of a chart `U` of the quotient data, as a `K`-scheme (i.e. `Spec (Γ(X,U)^Γ)` with
its structure morphism to `Spec K`). -/
noncomputable def chartU (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) : Work.SpecLin.Sch K :=
  Over.mk (D.chartι U ≫ (relQuotScheme X D hbase).hom)

/-- The invariant affine open subscheme `U` of `X`, as a `K`-scheme. -/
noncomputable def ovU {D : QuotientData Γ X.left} (U : D.Chart) : Work.SpecLin.Sch K :=
  Over.mk (U.1.ι ≫ X.hom)

/-- An affine open subscheme `V` of `Y`, as a `K`-scheme. -/
noncomputable def ovV (V : Y.left.affineOpens) : Work.SpecLin.Sch K :=
  Over.mk (V.1.ι ≫ Y.hom)

/-- The inclusion of the chart of `U` into the quotient, as a morphism of `K`-schemes. -/
noncomputable def chartιOv (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    chartU D hbase U ⟶ relQuotScheme X D hbase :=
  Over.homMk (D.chartι U) rfl

/-- The inclusion of `U` into `X`, as a morphism of `K`-schemes. -/
noncomputable def ovIncl {D : QuotientData Γ X.left} (U : D.Chart) : ovU U ⟶ X :=
  Over.homMk U.1.ι rfl

/-- The inclusion of `V` into `Y`, as a morphism of `K`-schemes. -/
noncomputable def ovVι (V : Y.left.affineOpens) : ovV V ⟶ Y :=
  Over.homMk V.1.ι rfl

@[simp] lemma chartU_hom (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    (chartU D hbase U).hom = D.chartι U ≫ (relQuotScheme X D hbase).hom := rfl

@[simp] lemma ovU_hom {D : QuotientData Γ X.left} (U : D.Chart) :
    (ovU U).hom = U.1.ι ≫ X.hom := rfl

@[simp] lemma ovV_hom (V : Y.left.affineOpens) : (ovV V).hom = V.1.ι ≫ Y.hom := rfl

@[simp] lemma ovU_left {D : QuotientData Γ X.left} (U : D.Chart) :
    (ovU U).left = U.1.toScheme := rfl

@[simp] lemma ovV_left (V : Y.left.affineOpens) : (ovV V).left = V.1.toScheme := rfl

@[simp] lemma relQuotSchemeMap_left (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    (relQuotSchemeMap X D hbase).left = D.quotientMap := rfl

@[simp] lemma relQuotScheme_hom (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    (relQuotScheme X D hbase).hom = D.quotientHom X.hom hbase := rfl

/-- **The quotient map on the piece `U`**: `U ⟶ Spec Γ(X,U)^Γ` (i.e. the chart map of `U`),
regarded as a morphism of `K`-schemes. -/
noncomputable def chartMapOv (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    ovU (D := D) U ⟶ chartU D hbase U :=
  Over.homMk (D.action.chartMap U.1 U.2.2) (by
    have h1 : D.action.chartMap U.1 U.2.2 ≫ D.chartι U = U.1.ι ≫ D.quotientMap :=
      (QuotientData.quotientMap_chartι D U).symm
    have h2 := QuotientData.quotientMap_quotientHom D X.hom hbase
    rw [chartU_hom, ovU_hom, relQuotScheme_hom, ← Category.assoc, h1, Category.assoc, h2])

/-- **The action of `Γ` on the piece `U`**, i.e. the restriction of the action of `D` on `X`
to the invariant open subscheme `U`. -/
noncomputable def actU (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (g : Γ) :
    ovU (D := D) U ⟶ ovU (D := D) U :=
  Over.homMk ((D.action.hom g).resLE U.1 U.1 (le_of_eq (U.2.2 g).symm)) (by
    have h1 : (D.action.hom g).resLE U.1 U.1 (le_of_eq (U.2.2 g).symm) ≫ U.1.ι
        = U.1.ι ≫ D.action.hom g :=
      Scheme.Hom.resLE_comp_ι (D.action.hom g) (le_of_eq (U.2.2 g).symm)
    rw [ovU_hom, ← Category.assoc, h1, Category.assoc, hbase g])

@[simp] lemma chartιOv_left (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    (chartιOv D hbase U).left = D.chartι U := rfl

@[simp] lemma ovIncl_left {D : QuotientData Γ X.left} (U : D.Chart) : (ovIncl U).left = U.1.ι := rfl

@[simp] lemma ovVι_left (V : Y.left.affineOpens) : (ovVι V).left = V.1.ι := rfl

@[simp] lemma chartMapOv_left (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    (chartMapOv D hbase U).left = D.action.chartMap U.1 U.2.2 := rfl

@[simp] lemma actU_left (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (g : Γ) :
    (actU D hbase U g).left = (D.action.hom g).resLE U.1 U.1 (le_of_eq (U.2.2 g).symm) := rfl

/-- The square `U ⟶ Spec Γ(X,U)^Γ ⟶ X/Γ` equals `U ⟶ X ⟶ X/Γ`. -/
theorem chartMapOv_chartιOv (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) :
    chartMapOv D hbase U ≫ chartιOv D hbase U = ovIncl (D := D) U ≫ relQuotSchemeMap X D hbase := by
  apply Over.OverMorphism.ext
  show (chartMapOv D hbase U).left ≫ (chartιOv D hbase U).left
    = (ovIncl (D := D) U).left ≫ (relQuotSchemeMap X D hbase).left
  rw [chartMapOv_left, chartιOv_left, ovIncl_left, relQuotSchemeMap_left]
  exact (QuotientData.quotientMap_chartι D U).symm

/-- The restriction of the action to `U` is compatible with the inclusion `U ⟶ X`. -/
theorem actU_ovIncl (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (g : Γ) :
    actU D hbase U g ≫ ovIncl (D := D) U = ovIncl (D := D) U ≫ actOver X D hbase g := by
  apply Over.OverMorphism.ext
  show (actU D hbase U g).left ≫ (ovIncl (D := D) U).left
    = (ovIncl (D := D) U).left ≫ (actOver X D hbase g).left
  rw [actU_left, ovIncl_left]
  exact Scheme.Hom.resLE_comp_ι (D.action.hom g) (le_of_eq (U.2.2 g).symm)

end Pieces

end Work.SymQuot.RelQuot
