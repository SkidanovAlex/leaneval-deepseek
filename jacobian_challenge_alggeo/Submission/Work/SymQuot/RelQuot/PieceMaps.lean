/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The pieces of the relative quotient `(X/Γ) ⊗ Y` (area SY, `relQuot`)

For a chart `U` of a quotient datum `D` and an affine open `V ⊆ Y`, the *piece* of the relative
quotient `(X/Γ) ⊗ Y` is `(chart U) ⊗ V`, and the *piece* of `X ⊗ Y` is `U ⊗ V`.  This file
provides the structural morphisms between the pieces

* `chartResOv` — the inclusion `chart U ⟶ chart U'` for `U ≤ U'`;
* `ovUMap`, `ovVMap` — the inclusions `U ⟶ U'`, `V ⟶ V'`;
* `pieceTrans` — the transition map `(chart U) ⊗ V ⟶ (chart U') ⊗ V'` of the piece cover;

together with the naturality statements that make the pieces a diagram over the quotient:

* `chartResOv_chartιOv` — `chart U ⟶ chart U' ⟶ X/Γ` equals `chart U ⟶ X/Γ`;
* `chartMapOv_ovUMap_chartResOv` — the square `U ⟶ chart U ⟶ chart U'` vs
  `U ⟶ U' ⟶ chart U'` (`Work.SymQuot.Chart.chartRes_chartMap`);
* `pieceTrans_comp` — the compatibility of the transition maps with the cover maps;
* `chartMapOv_pieceTrans`, `ovIncl_tensor_quot`, `actU_tensor_ovIncl`,
  `actU_tensor_invariant` — the naturality squares of the quotient map of a piece, of the map
  `q ▷ Y`, and the invariance of the restriction of an invariant morphism.
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.Chart.chartRes_chartMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical MonoidalCategory

namespace Work.SymQuot.RelQuot

variable {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ] {X Y : Work.SpecLin.Sch K}

lemma chartResOv_w (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} (h : U ≤ U') :
    D.action.chartRes U.1 U'.1 h U'.2.2 U.2.2 ≫ D.chartι U' = D.chartι U :=
  colimit.w D.chartFunctor (homOfLE h)

noncomputable def chartResOv (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} (h : U ≤ U') :
    chartU D hbase U ⟶ chartU D hbase U' :=
  Over.homMk (D.action.chartRes U.1 U'.1 h U'.2.2 U.2.2) (by
    rw [chartU_hom, chartU_hom, relQuotScheme_hom, ← Category.assoc, chartResOv_w D hbase h])

noncomputable def ovUMap (D : QuotientData Γ X.left) {U U' : D.Chart} (h : U ≤ U') :
    ovU (D := D) U ⟶ ovU (D := D) U' :=
  Over.homMk (Scheme.homOfLE X.left h) (by
    rw [ovU_hom, ovU_hom, ← Category.assoc, Scheme.homOfLE_ι])

noncomputable def ovVMap {V V' : Y.left.affineOpens} (h : V ≤ V') : ovV V ⟶ ovV V' :=
  Over.homMk (Scheme.homOfLE Y.left h) (by
    rw [ovV_hom, ovV_hom, ← Category.assoc, Scheme.homOfLE_ι])

@[simp] lemma chartResOv_left (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} (h : U ≤ U') :
    (chartResOv D hbase h).left = D.action.chartRes U.1 U'.1 h U'.2.2 U.2.2 := rfl

@[simp] lemma ovUMap_left (D : QuotientData Γ X.left) {U U' : D.Chart} (h : U ≤ U') :
    (ovUMap (D := D) h).left = Scheme.homOfLE X.left h := rfl

@[simp] lemma ovVMap_left {V V' : Y.left.affineOpens} (h : V ≤ V') :
    (ovVMap (Y := Y) h).left = Scheme.homOfLE Y.left h := rfl

lemma ovUMap_ovIncl (D : QuotientData Γ X.left) {U U' : D.Chart} (h : U ≤ U') :
    ovUMap (D := D) h ≫ ovIncl (D := D) U' = ovIncl (D := D) U := by
  apply Over.OverMorphism.ext
  show (ovUMap (D := D) h).left ≫ (ovIncl (D := D) U').left = (ovIncl (D := D) U).left
  rw [ovUMap_left, ovIncl_left, ovIncl_left]
  exact Scheme.homOfLE_ι X.left h

lemma chartResOv_chartιOv (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} (h : U ≤ U') :
    chartResOv D hbase h ≫ chartιOv D hbase U' = chartιOv D hbase U := by
  apply Over.OverMorphism.ext
  show (chartResOv D hbase h).left ≫ (chartιOv D hbase U').left = (chartιOv D hbase U).left
  rw [chartResOv_left, chartιOv_left, chartιOv_left]
  exact chartResOv_w D hbase h

lemma ovVMap_ovVι {V V' : Y.left.affineOpens} (h : V ≤ V') :
    ovVMap (Y := Y) h ≫ ovVι V' = ovVι V := by
  apply Over.OverMorphism.ext
  show (ovVMap (Y := Y) h).left ≫ (ovVι V').left = (ovVι V).left
  rw [ovVMap_left, ovVι_left, ovVι_left]
  exact Scheme.homOfLE_ι Y.left h

lemma chartMapOv_ovUMap_chartResOv (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} (h : U ≤ U') :
    chartMapOv D hbase U ≫ chartResOv D hbase h = ovUMap (D := D) h ≫ chartMapOv D hbase U' := by
  apply Over.OverMorphism.ext
  show (chartMapOv D hbase U).left ≫ (chartResOv D hbase h).left
    = (ovUMap (D := D) h).left ≫ (chartMapOv D hbase U').left
  rw [chartMapOv_left, chartResOv_left, ovUMap_left, chartMapOv_left]
  exact (Work.SymQuot.Chart.chartRes_chartMap D.action h U'.2.2 U.2.2).symm

/-- The transition map of the piece cover. -/
noncomputable def pieceTrans (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} {V V' : Y.left.affineOpens}
    (h : U ≤ U') (h' : V ≤ V') :
    chartU D hbase U ⊗ ovV V ⟶ chartU D hbase U' ⊗ ovV V' :=
  chartResOv D hbase h ⊗ₘ ovVMap (Y := Y) h'

/-- Composition of right whiskerings. -/
lemma whiskerRight_comp' {C : Type*} [Category C] [MonoidalCategory C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : C) : (f ▷ W) ≫ (g ▷ W) = (f ≫ g) ▷ W := by
  rw [← MonoidalCategory.tensorHom_id g W, MonoidalCategory.whiskerRight_comp_tensorHom,
    MonoidalCategory.tensorHom_id]

lemma pieceTrans_comp (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} {V V' : Y.left.affineOpens}
    (h : U ≤ U') (h' : V ≤ V') :
    pieceTrans D hbase h h' ≫ (chartιOv D hbase U' ⊗ₘ ovVι V')
      = (chartιOv D hbase U ⊗ₘ ovVι V) := by
  rw [pieceTrans, MonoidalCategory.tensorHom_comp_tensorHom, chartResOv_chartιOv D hbase h,
    ovVMap_ovVι h']

/-- **Naturality of the quotient map of a piece** with respect to the transition maps. -/
lemma chartMapOv_pieceTrans (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} {V V' : Y.left.affineOpens}
    (h : U ≤ U') (h' : V ≤ V') :
    (chartMapOv D hbase U ▷ ovV V) ≫ pieceTrans D hbase h h'
      = (ovUMap (D := D) h ⊗ₘ ovVMap (Y := Y) h') ≫ (chartMapOv D hbase U' ▷ ovV V') := by
  rw [pieceTrans, MonoidalCategory.whiskerRight_comp_tensorHom,
    chartMapOv_ovUMap_chartResOv D hbase h, ← MonoidalCategory.tensorHom_comp_whiskerRight
      (ovUMap (D := D) h) (chartMapOv D hbase U') (ovVMap (Y := Y) h')]

/-- The transition map of the source pieces is compatible with the inclusion into `X ⊗ Y`. -/
lemma ovUMap_tensor_ovVMap (D : QuotientData Γ X.left) {U U' : D.Chart} {V V' : Y.left.affineOpens}
    (h : U ≤ U') (h' : V ≤ V') :
    (ovUMap (D := D) h ⊗ₘ ovVMap (Y := Y) h') ≫ (ovIncl (D := D) U' ⊗ₘ ovVι V')
      = (ovIncl (D := D) U ⊗ₘ ovVι V) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom (ovUMap (D := D) h) (ovVMap (Y := Y) h')
      (ovIncl (D := D) U') (ovVι V'), ovUMap_ovIncl D h, ovVMap_ovVι h']

/-- The square exhibiting the quotient map `q ▷ Y` on a piece. -/
lemma ovIncl_tensor_quot (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (V : Y.left.affineOpens) :
    (ovIncl (D := D) U ⊗ₘ ovVι V) ≫ (relQuotSchemeMap X D hbase ▷ Y)
      = (chartMapOv D hbase U ▷ ovV V) ≫ (chartιOv D hbase U ⊗ₘ ovVι V) := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc, whiskerRight_comp',
    ← chartMapOv_chartιOv D hbase U, ← whiskerRight_comp', ← Category.assoc,
    ← MonoidalCategory.tensorHom_def' (chartMapOv D hbase U) (ovVι V),
    MonoidalCategory.tensorHom_def, Category.assoc,
    ← MonoidalCategory.tensorHom_def' (chartιOv D hbase U) (ovVι V)]

/-- The invariance of the restriction of an invariant morphism to a piece. -/
lemma actU_tensor_ovIncl (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (V : Y.left.affineOpens)
    (g : Γ) :
    (actU D hbase U g ▷ ovV V) ≫ (ovIncl (D := D) U ⊗ₘ ovVι V)
      = (ovIncl (D := D) U ⊗ₘ ovVι V) ≫ (actOver X D hbase g ▷ Y) := by
  calc (actU D hbase U g ▷ ovV V) ≫ (ovIncl (D := D) U ⊗ₘ ovVι V)
      = (actU D hbase U g ▷ ovV V) ≫
          ((ovU (D := D) U ◁ ovVι V) ≫ (ovIncl (D := D) U ▷ Y)) := by
        rw [MonoidalCategory.tensorHom_def']
    _ = ((actU D hbase U g ▷ ovV V) ≫ (ovU (D := D) U ◁ ovVι V)) ≫
          (ovIncl (D := D) U ▷ Y) := by
        rw [← Category.assoc]
    _ = ((ovU (D := D) U ◁ ovVι V) ≫ (actU D hbase U g ▷ Y)) ≫
          (ovIncl (D := D) U ▷ Y) := by
        rw [← MonoidalCategory.whisker_exchange (actU D hbase U g) (ovVι V)]
    _ = (ovU (D := D) U ◁ ovVι V) ≫
          ((actU D hbase U g ▷ Y) ≫ (ovIncl (D := D) U ▷ Y)) := by
        rw [Category.assoc]
    _ = (ovU (D := D) U ◁ ovVι V) ≫
          ((actU D hbase U g ≫ ovIncl (D := D) U) ▷ Y) := by
        rw [whiskerRight_comp']
    _ = (ovU (D := D) U ◁ ovVι V) ≫
          ((ovIncl (D := D) U ≫ actOver X D hbase g) ▷ Y) := by
        rw [actU_ovIncl D hbase U g]
    _ = (ovIncl (D := D) U ≫ actOver X D hbase g) ⊗ₘ ovVι V := by
        rw [← MonoidalCategory.tensorHom_def' (ovIncl (D := D) U ≫ actOver X D hbase g) (ovVι V)]
    _ = (ovIncl (D := D) U ⊗ₘ ovVι V) ≫ (actOver X D hbase g ▷ Y) := by
        rw [← MonoidalCategory.tensorHom_comp_whiskerRight (ovIncl (D := D) U)
          (actOver X D hbase g) (ovVι V)]

lemma actU_tensor_invariant (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (V : Y.left.affineOpens)
    {Z : Work.SpecLin.Sch K} (f : X ⊗ Y ⟶ Z) (hf : ∀ g : Γ, (actOver X D hbase g ▷ Y) ≫ f = f)
    (g : Γ) :
    (actU D hbase U g ▷ ovV V) ≫ ((ovIncl (D := D) U ⊗ₘ ovVι V) ≫ f)
      = (ovIncl (D := D) U ⊗ₘ ovVι V) ≫ f := by
  rw [← Category.assoc, actU_tensor_ovIncl D hbase U V g, Category.assoc, hf g]

end Work.SymQuot.RelQuot
