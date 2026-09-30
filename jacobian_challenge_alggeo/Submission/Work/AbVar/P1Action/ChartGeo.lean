/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — equivariance of the orbit map.

We prove that the orbit map `gmToP1 k : 𝔾_m ⟶ ℙ¹`, `T ↦ [T : 1]`, is equivariant for the scaling
action `scalingAct k : ℙ¹ ⊗ 𝔾_m ⟶ ℙ¹`, i.e. `(gmToP1 ⊗ id) ≫ scalingAct = μ ≫ gmToP1`.

The computation is made on the chart `D₊(X₁)` of `ℙ¹`, which contains the image of `gmToP1`.  The
morphism `gmToP1 ⊗ id` factors through the chart `srcChartι k 1 = D₊(X₁) × 𝔾_m` of the source,
with chart-coordinate map `a ⊗ t ↦ chartEvalT a ⊗ t`.  Composing with the chart description
`thetaRing k 1` of the action (which sends `X₀/X₁` to `(X₀/X₁) ⊗ T`) yields the ring map
`x ↦ chartEvalT x ⊗ chartEvalT x`, which is exactly the composite `comul ∘ chartEvalT` appearing in
`μ ≫ gmToP1` (the group law of `𝔾_m` being comultiplication `T ↦ T ⊗ T`).
-/
import Mathlib
import Submission.Work.AbVar.P1Action.ChartMaps
import Submission.Work.AbVar.P1Action.Action

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-- The `k`-algebra map `chartRing k 1 ⊗[k] k[T;T⁻¹] → k[T;T⁻¹] ⊗[k] k[T;T⁻¹]`,
`a ⊗ t ↦ chartEvalT a ⊗ t`: the chart-`D₊(X₁)` coordinate description of `gmToP1 ⊗ id`. -/
noncomputable abbrev mapChartEvalT : srcChartRing k 1 →ₐ[k] L k ⊗[k] L k :=
  Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k))

/-- The chart-coordinate morphism of `gmToP1 ⊗ id` on the chart `D₊(X₁) × 𝔾_m` of the source. -/
noncomputable def psiQ :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k (L k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k (L k))))
      ⟶ Spec (CommRingCat.of (srcChartRing k 1)) :=
  (pullbackSpecIso k (L k) (L k)).hom
    ≫ Spec.map (CommRingCat.ofHom (mapChartEvalT k).toRingHom)

lemma mapChartEvalT_includeLeft :
    (mapChartEvalT k).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := chartRing k 1) (B := L k))
      = (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := L k) (B := L k)).comp
          (chartEvalT k) := by
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply, RingHom.comp_apply]
  change (mapChartEvalT k) (a ⊗ₜ[k] (1 : L k))
      = Algebra.TensorProduct.includeLeftRingHom (R := k) (A := L k) (B := L k) (chartEvalT k a)
  rw [mapChartEvalT, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply, chartEvalTAlgHom_apply]

lemma mapChartEvalT_includeRight :
    (mapChartEvalT k).toRingHom.comp (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 1) (B := L k)))
      = (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k) (A := L k)
          (B := L k))) := by
  apply RingHom.ext
  intro t
  rw [RingHom.comp_apply]
  change (mapChartEvalT k)
      (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 1) (B := L k) t)
    = Algebra.TensorProduct.includeRight (R := k) (A := L k) (B := L k) t
  rw [Algebra.TensorProduct.includeRight_apply, mapChartEvalT, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply, map_one]

/-- First projection of `psiQ`. -/
lemma psiQ_includeLeft :
    psiQ k ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := chartRing k 1) (B := L k)))
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (L k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k (L k))))
          ≫ Spec.map (CommRingCat.ofHom (chartEvalT k)) := by
  rw [psiQ, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← pullbackSpecIso_hom_fst k (L k) (L k), Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← mapChartEvalT_includeLeft]

/-- Second projection of `psiQ`. -/
lemma psiQ_includeRight :
    psiQ k ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 1) (B := L k))))
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k (L k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k (L k)))) := by
  rw [psiQ, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    mapChartEvalT_includeRight, pullbackSpecIso_hom_snd k (L k) (L k)]

open CategoryTheory.MonoidalCategoryStruct in
/-- The morphism `gmToP1 ⊗ id` factors through the chart `D₊(X₁) × 𝔾_m` of the source. -/
theorem tensorHom_gmToP1_left :
    Over.Hom.left (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
        (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k)))
      = psiQ k ≫ srcChartι k 1 := by
  apply pullback.hom_ext (f := (Work.AbVar.P1 k).hom) (g := gmHom k)
  · change Over.Hom.left (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
          (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k)))
        ≫ pullback.fst (Work.AbVar.P1 k).hom (Work.AbVar.Gm k).hom
      = (psiQ k ≫ srcChartι k 1) ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k)
    rw [Over.tensorHom_left_fst (fS := (Work.AbVar.P1 k).hom) (fU := (Work.AbVar.Gm k).hom)
      (f := gmToP1 k) (g := CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k))]
    rw [Category.assoc, srcChartι_fst, ← Category.assoc, psiQ_includeLeft, Category.assoc]
    rfl
  · change Over.Hom.left (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
          (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k)))
        ≫ pullback.snd (Work.AbVar.P1 k).hom (Work.AbVar.Gm k).hom
      = (psiQ k ≫ srcChartι k 1) ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k)
    rw [Over.tensorHom_left_snd (fS := (Work.AbVar.P1 k).hom) (fU := (Work.AbVar.Gm k).hom)
      (f := gmToP1 k) (g := CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k))]
    rw [Over.id_left, Category.comp_id, Category.assoc, srcChartι_snd, psiQ_includeRight]
    rfl

/-- `psiQ` composed with the chart description of the action in chart `1`. -/
lemma psiQ_thetaRing :
    psiQ k ≫ Spec.map (CommRingCat.ofHom (thetaRing k 1))
      = (pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom ((mapChartEvalT k).toRingHom.comp (thetaRing k 1))) := by
  rw [psiQ, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- `Over.Hom.left` of `tensorHom gmToP1 id ≫ scalingAct`, computed on the chart `D₊(X₁)`. -/
theorem left_equivariance :
    Over.Hom.left (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
          (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k)))
        (scalingAct k))
      = (pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom ((mapChartEvalT k).toRingHom.comp (thetaRing k 1)))
          ≫ chartObjHom k 1 := by
  have e1 : Over.Hom.left (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
          (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k)))
        (scalingAct k))
      = Over.Hom.left (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
          (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k))) ≫ scalingActLeft k := by
    rw [Over.comp_left]; rfl
  have e2 : Over.Hom.left (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
        (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k))) ≫ scalingActLeft k
      = (psiQ k ≫ srcChartι k 1) ≫ scalingActLeft k :=
    congrArg (fun t => t ≫ scalingActLeft k) (tensorHom_gmToP1_left k)
  have e3 : (psiQ k ≫ srcChartι k 1) ≫ scalingActLeft k
      = (pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom ((mapChartEvalT k).toRingHom.comp (thetaRing k 1)))
          ≫ chartObjHom k 1 := by
    rw [Category.assoc, srcChartι_scalingActLeft,
      show srcChartHom k 1 = Spec.map (CommRingCat.ofHom (thetaRing k 1)) ≫ chartObjHom k 1
        from rfl,
      ← Category.assoc, psiQ_thetaRing, Category.assoc]
  exact e1.trans (e2.trans e3)

/-- `Over.Hom.left` of `μ ≫ gmToP1`, computed on the chart `D₊(X₁)`. -/
theorem right_equivariance :
    Over.Hom.left (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonObj.mul (X := Work.AbVar.Gm k)) (gmToP1 k))
      = (pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom ((Bialgebra.comulAlgHom k (L k)).toRingHom.comp
              (chartEvalT k)))
          ≫ chartObjHom k 1 := by
  have e1 : Over.Hom.left (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonObj.mul (X := Work.AbVar.Gm k)) (gmToP1 k))
      = μ[Work.AbVar.Gm k].left ≫ Over.Hom.left (gmToP1 k) := by
    rw [Over.comp_left]
  have e2 : μ[Work.AbVar.Gm k].left ≫ Over.Hom.left (gmToP1 k)
      = ((pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (L k)).toRingHom))
        ≫ (Spec.map (CommRingCat.ofHom (chartEvalT k)) ≫ chartObjHom k 1) := by
    rw [show μ[Work.AbVar.Gm k].left = (pullbackSpecIso k (L k) (L k)).hom
        ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (L k)).toRingHom) from
      mul_spec_asOver_spec_left,
      show Over.Hom.left (gmToP1 k)
        = Spec.map (CommRingCat.ofHom (chartEvalT k)) ≫ chartObjHom k 1 from rfl]
    rfl
  have e3 : ((pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (L k)).toRingHom))
        ≫ (Spec.map (CommRingCat.ofHom (chartEvalT k)) ≫ chartObjHom k 1)
      = (pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom ((Bialgebra.comulAlgHom k (L k)).toRingHom.comp
              (chartEvalT k)))
          ≫ chartObjHom k 1 := by
    rw [Category.assoc, ← Category.assoc
        (Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (L k)).toRingHom))
        (Spec.map (CommRingCat.ofHom (chartEvalT k))) (chartObjHom k 1),
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact e1.trans (e2.trans e3)

/-- The ring identity expressing the equivariance. -/
theorem mapChartEvalT_comp_thetaRing :
    (mapChartEvalT k).toRingHom.comp (thetaRing k 1)
      = (Bialgebra.comulAlgHom k (L k)).toRingHom.comp (chartEvalT k) := by
  apply RingHom.ext
  intro x
  exact map_thetaRing_one k x

/-- **The orbit map `𝔾_m ⟶ ℙ¹`, `T ↦ [T : 1]`, is equivariant for the scaling action.** -/
theorem scalingAct_equivariance_aux :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategoryStruct.tensorHom (gmToP1 k)
          (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k)))
        (scalingAct k)
      = CategoryTheory.CategoryStruct.comp (CategoryTheory.MonObj.mul (X := Work.AbVar.Gm k))
          (gmToP1 k) := by
  apply Over.OverMorphism.ext
  have hmid : (pullbackSpecIso k (L k) (L k)).hom
        ≫ Spec.map (CommRingCat.ofHom ((mapChartEvalT k).toRingHom.comp (thetaRing k 1)))
        ≫ chartObjHom k 1
      = (pullbackSpecIso k (L k) (L k)).hom
          ≫ Spec.map (CommRingCat.ofHom ((Bialgebra.comulAlgHom k (L k)).toRingHom.comp
              (chartEvalT k)))
          ≫ chartObjHom k 1 := by
    rw [mapChartEvalT_comp_thetaRing]
  exact (left_equivariance k).trans (hmid.trans (right_equivariance k).symm)

end

end Work.AbVar.P1Action
