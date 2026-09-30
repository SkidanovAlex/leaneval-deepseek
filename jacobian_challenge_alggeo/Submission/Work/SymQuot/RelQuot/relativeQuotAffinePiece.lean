import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.RelQuot.tensorIncl_range
import Submission.Work.SymQuot.RelQuot.specFixedPoints_lift
import Submission.Work.SymQuot.RelQuot.relativeQuotAffinePieceAux
import Submission.Work.SymQuot.RelQuot.specTensorIso_naturality
import Submission.Work.SymQuot.RelQuot.specOf_tensorIncl_factor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical MonoidalCategory

universe u
open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem relativeQuotAffinePiece {K : Type u} [Field K] {X Y : Work.SpecLin.Sch K} {Γ : Type u}
    [Group Γ] [Fintype Γ] (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (U : D.Chart) (V : Y.left.affineOpens)
    {Z : Work.SpecLin.Sch K}
    (f : Work.SymQuot.RelQuot.ovU (D := D) U ⊗ Work.SymQuot.RelQuot.ovV V ⟶ Z)
    (hf : ∀ g : Γ, (Work.SymQuot.RelQuot.actU D hbase U g ▷ Work.SymQuot.RelQuot.ovV V) ≫ f = f) :
    ∃! h : Work.SymQuot.RelQuot.chartU D hbase U ⊗ Work.SymQuot.RelQuot.ovV V ⟶ Z,
      (Work.SymQuot.RelQuot.chartMapOv D hbase U ▷ Work.SymQuot.RelQuot.ovV V) ≫ h = f := by

  classical
  letI : MulSemiringAction Γ ↥Γ(X.left, U.1) := D.action.sectionMulSemiringAction U.1 U.2.2
  letI : SMulCommClass Γ K ↥Γ(X.left, U.1) := smulCommClassSections X D.action U.2.2 hbase
  let e1 : ovU (D := D) U ⊗ ovV (Y := Y) V ≅
      Work.SpecLin.specOf (K := K) (↥Γ(X.left, U.1) ⊗[K] ↥Γ(Y.left, V.1)) :=
    (ovUIsoSpecOf D U ⊗ᵢ ovVIsoSpecOf (K := K) V) ≪≫
      specTensorIso (K := K) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)
  let e2 : chartU D hbase U ⊗ ovV (Y := Y) V ≅
      Work.SpecLin.specOf (K := K)
        (↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ) ⊗[K] ↥Γ(Y.left, V.1)) :=
    (chartIsoSpecOf D hbase U ⊗ᵢ ovVIsoSpecOf (K := K) V) ≪≫
      specTensorIso (K := K) ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ) ↥Γ(Y.left, V.1)
  have he1h : e1.hom = ((ovUIsoSpecOf D U).hom ⊗ₘ (ovVIsoSpecOf (K := K) V).hom) ≫
      (specTensorIso (K := K) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)).hom := rfl
  have he1i : e1.inv = (specTensorIso (K := K) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)).inv ≫
      ((ovUIsoSpecOf D U).inv ⊗ₘ (ovVIsoSpecOf (K := K) V).inv) := rfl
  have he2h : e2.hom = ((chartIsoSpecOf D hbase U).hom ⊗ₘ (ovVIsoSpecOf (K := K) V).hom) ≫
      (specTensorIso (K := K) ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ)
        ↥Γ(Y.left, V.1)).hom := rfl
  -- the action square
  have hS2 : ∀ g : Γ, (actU D hbase U g ▷ ovV (Y := Y) V) ≫ e1.hom = e1.hom ≫
      Work.SpecLin.specOfMap
        (tensorAct (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1) g⁻¹) := by
    intro g
    have hM := specTensorIso_naturality (K := K)
      (A₁ := ↥Γ(X.left, U.1)) (A₂ := ↥Γ(X.left, U.1))
      (B₁ := ↥Γ(Y.left, V.1)) (B₂ := ↥Γ(Y.left, V.1))
      (MulSemiringAction.toAlgHom K ↥Γ(X.left, U.1) g⁻¹) (AlgHom.id K ↥Γ(Y.left, V.1))
    rw [Work.SpecLin.specOfMap_id] at hM
    have hconj := tensorHom_conj (ovUIsoSpecOf D U) (ovVIsoSpecOf (K := K) V)
      (actU D hbase U g)
    have hcompat := ovUIsoSpecOf_actU D hbase U g
    rw [he1h]
    show (actU D hbase U g ⊗ₘ 𝟙 (ovV (Y := Y) V)) ≫
          (((ovUIsoSpecOf D U).hom ⊗ₘ (ovVIsoSpecOf (K := K) V).hom) ≫
            (specTensorIso (K := K) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)).hom)
        = (((ovUIsoSpecOf D U).hom ⊗ₘ (ovVIsoSpecOf (K := K) V).hom) ≫
            (specTensorIso (K := K) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)).hom) ≫
            Work.SpecLin.specOfMap
              (tensorAct (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1) g⁻¹)
    rw [← Category.assoc, hconj, hcompat, Category.assoc, hM, Category.assoc]
    rfl
  -- the chart square
  have hgm : chartMapOv D hbase U ≫ (chartIsoSpecOf D hbase U).hom =
      (ovUIsoSpecOf D U).hom ≫
        Work.SpecLin.specOfMap (FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ).val := by
    calc chartMapOv D hbase U ≫ (chartIsoSpecOf D hbase U).hom
        = 𝟙 _ ≫ chartMapOv D hbase U ≫ (chartIsoSpecOf D hbase U).hom :=
          (Category.id_comp _).symm
      _ = ((ovUIsoSpecOf D U).hom ≫ (ovUIsoSpecOf D U).inv) ≫
            chartMapOv D hbase U ≫ (chartIsoSpecOf D hbase U).hom := by rw [Iso.hom_inv_id]
      _ = (ovUIsoSpecOf D U).hom ≫
            ((ovUIsoSpecOf D U).inv ≫ chartMapOv D hbase U ≫ (chartIsoSpecOf D hbase U).hom) := by
          rw [Category.assoc]
      _ = (ovUIsoSpecOf D U).hom ≫
            Work.SpecLin.specOfMap (FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ).val := by
          rw [chartIsoSpecOf_chartMapOv]
  have hS1 : (chartMapOv D hbase U ▷ ovV (Y := Y) V) ≫ e2.hom = e1.hom ≫
      Work.SpecLin.specOfMap
        (tensorIncl (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)) := by
    have hM := specTensorIso_naturality (K := K)
      (A₁ := ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ)) (A₂ := ↥Γ(X.left, U.1))
      (B₁ := ↥Γ(Y.left, V.1)) (B₂ := ↥Γ(Y.left, V.1))
      (FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ).val (AlgHom.id K ↥Γ(Y.left, V.1))
    rw [Work.SpecLin.specOfMap_id] at hM
    have hconj := tensorHom_conjIso (chartMapOv D hbase U) (chartIsoSpecOf D hbase U)
      (ovUIsoSpecOf D U) (Work.SpecLin.specOfMap (FixedPoints.subalgebra K ↥Γ(X.left,U.1) Γ).val)
      (ovVIsoSpecOf (K := K) V) hgm
    rw [he2h, he1h]
    show (chartMapOv D hbase U ⊗ₘ 𝟙 (ovV (Y := Y) V)) ≫
          (((chartIsoSpecOf D hbase U).hom ⊗ₘ (ovVIsoSpecOf (K := K) V).hom) ≫
            (specTensorIso (K := K) ↥(FixedPoints.subalgebra K ↥Γ(X.left, U.1) Γ)
              ↥Γ(Y.left, V.1)).hom)
        = (((ovUIsoSpecOf D U).hom ⊗ₘ (ovVIsoSpecOf (K := K) V).hom) ≫
            (specTensorIso (K := K) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)).hom) ≫
            Work.SpecLin.specOfMap
              (tensorIncl (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1))
    rw [← Category.assoc, hconj, Category.assoc, hM, Category.assoc]
    rfl
  -- existence
  obtain ⟨h', hh', huniq'⟩ := specOf_tensorIncl_factor (K := K) (Γ := Γ)
    (A := ↥Γ(X.left, U.1)) (B := ↥Γ(Y.left, V.1)) (Z := Z) (f := e1.inv ≫ f) (hf := by
      intro g
      have h := hS2 g⁻¹
      simp only [inv_inv] at h
      have hL : e1.hom ≫
          (Work.SpecLin.specOfMap
            (tensorAct (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1) g) ≫ e1.inv ≫ f)
          = f := by
        rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_assoc, hf g⁻¹]
      have hR : e1.hom ≫ (e1.inv ≫ f) = f := by rw [Iso.hom_inv_id_assoc]
      exact (cancel_epi e1.hom).mp (hL.trans hR.symm))
  refine ⟨e2.hom ≫ h', ?_, ?_⟩
  · show (chartMapOv D hbase U ▷ ovV (Y := Y) V) ≫ (e2.hom ≫ h') = f
    rw [← Category.assoc, hS1, Category.assoc, hh', Iso.hom_inv_id_assoc]
  · intro h hh
    have hspec : Work.SpecLin.specOfMap
        (tensorIncl (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1))
        = e1.inv ≫ (chartMapOv D hbase U ▷ ovV (Y := Y) V) ≫ e2.hom := by
      calc Work.SpecLin.specOfMap
            (tensorIncl (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1))
          = e1.inv ≫ e1.hom ≫ Work.SpecLin.specOfMap
              (tensorIncl (K := K) (Γ := Γ) ↥Γ(X.left, U.1) ↥Γ(Y.left, V.1)) :=
            (Iso.inv_hom_id_assoc e1 _).symm
        _ = e1.inv ≫ ((chartMapOv D hbase U ▷ ovV (Y := Y) V) ≫ e2.hom) := by rw [hS1]
    have hkey : e2.inv ≫ h = h' := by
      apply huniq'
      rw [hspec]
      simp only [Category.assoc]
      rw [Iso.hom_inv_id_assoc, hh]
    rw [← hkey, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]


end Work.SymQuot.RelQuot
