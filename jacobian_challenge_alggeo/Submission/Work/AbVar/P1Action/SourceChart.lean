/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — the affine charts of the source `ℙ¹ ⊗ 𝔾_m`.

We work with the explicit model `srcScheme k = ℙ¹ ×_{Spec k} Spec k[T;T⁻¹]` of the underlying
scheme of `ℙ¹ ⊗ 𝔾_m`; the two charts are `D₊(Xᵢ) × 𝔾_m`, each of which is
`Spec (chartRing k i ⊗[k] k[T;T⁻¹])`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits RingHomClass
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

/-- The coordinate ring of `𝔾_m`. -/
abbrev L (k : Type*) [Field k] := LaurentPolynomial k

/-- The coordinate ring of the chart `D₊(Xᵢ) × 𝔾_m`. -/
abbrev srcChartRing (k : Type*) [Field k] (i : Fin 2) := chartRing k i ⊗[k] L k

section

variable (k : Type*) [Field k]

/-- The structure morphism of `𝔾_m`, as an explicit `Spec.map`. -/
noncomputable abbrev gmHom : Spec (CommRingCat.of (L k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (L k)))

lemma gm_hom : (Work.AbVar.Gm k).hom = gmHom k := by
  show (Spec (CommRingCat.of (L k)) ↘ Spec (CommRingCat.of k)) = _
  exact specOverSpec_over (R := CommRingCat.of k) (A := CommRingCat.of (L k))

/-- The underlying scheme of the source `ℙ¹ ⊗ 𝔾_m`. -/
noncomputable abbrev srcScheme : Scheme := pullback (Work.AbVar.P1 k).hom (gmHom k)

/-- The source `ℙ¹ ⊗ 𝔾_m` is the fibre product of `ℙ¹` with `Spec k[T;T⁻¹]`. -/
noncomputable def srcSchemeIso : srcScheme k ≅ (Work.AbVar.P1 k ⊗ Work.AbVar.Gm k).left :=
  pullback.congrHom (rfl : (Work.AbVar.P1 k).hom = (Work.AbVar.P1 k).hom) (gm_hom k).symm

/-- The pullback of the chart `D₊(Xᵢ)` along the projection `ℙ¹ ⊗ 𝔾_m ⟶ ℙ¹`. -/
noncomputable abbrev srcChartScheme (i : Fin 2) : Scheme :=
  pullback (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k)

/-- The inclusion of the chart `D₊(Xᵢ) × 𝔾_m` into the source. -/
noncomputable abbrev srcChartMap (i : Fin 2) : srcChartScheme k i ⟶ srcScheme k :=
  pullback.map (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k)
    (Work.AbVar.P1 k).hom (gmHom k) (chartObjHom k i) (𝟙 _) (𝟙 _)
    (by rw [Category.assoc, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

instance chartObjHom_isOpenImmersion (i : Fin 2) : IsOpenImmersion (chartObjHom k i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (Work.AbVar.ProjectiveLine.StdG k)
    (MvPolynomial.X i) (Work.AbVar.ProjectiveLine.X_mem_stdG i) (by norm_num)))

instance srcChartMap_isOpenImmersion (i : Fin 2) : IsOpenImmersion (srcChartMap k i) :=
  Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _

lemma srcChartMap_fst (i : Fin 2) :
    srcChartMap k i ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k)
      = pullback.fst (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k) ≫ chartObjHom k i := by
  simp only [srcChartMap, pullback.map, pullback.lift_fst, Category.comp_id]

lemma srcChartMap_snd (i : Fin 2) :
    srcChartMap k i ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k)
      = pullback.snd (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k) := by
  simp only [srcChartMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The identification of the chart `D₊(Xᵢ) × 𝔾_m` with `Spec (chartRing k i ⊗[k] k[T;T⁻¹])`. -/
noncomputable abbrev srcChartIso (i : Fin 2) :
    srcChartScheme k i ≅ Spec (CommRingCat.of (srcChartRing k i)) :=
  pullback.congrHom (chartObjHom_hom k i) (rfl : gmHom k = gmHom k) ≪≫
    pullbackSpecIso k (chartRing k i) (L k)

lemma srcChartIso_inv_fst (i : Fin 2) :
    (srcChartIso k i).inv ≫ pullback.fst (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k)
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := chartRing k i) (B := L k))) := by
  rw [← Iso.inv_hom_id_assoc (srcChartIso k i) (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := chartRing k i) (B := L k))))]
  congr 1
  simp only [srcChartIso, Iso.trans_hom, pullback.congrHom_hom, pullback.map, pullback.lift_fst,
    Category.comp_id, pullbackSpecIso_hom_fst, Category.assoc]

lemma srcChartIso_inv_snd (i : Fin 2) :
    (srcChartIso k i).inv ≫ pullback.snd (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k)
      = Spec.map (CommRingCat.ofHom
          ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k i) (B := L k))))) := by
  rw [← Iso.inv_hom_id_assoc (srcChartIso k i) (Spec.map (CommRingCat.ofHom
    ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k i) (B := L k))))))]
  congr 1
  simp only [srcChartIso, Iso.trans_hom, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
    Category.comp_id, Category.id_comp, pullbackSpecIso_hom_snd, Category.assoc]

/-- The chart of the source, as a morphism from `Spec (chartRing k i ⊗[k] k[T;T⁻¹])`. -/
noncomputable abbrev srcChartι (i : Fin 2) :
    Spec (CommRingCat.of (srcChartRing k i)) ⟶ srcScheme k :=
  (srcChartIso k i).inv ≫ srcChartMap k i

instance srcChartι_isOpenImmersion (i : Fin 2) : IsOpenImmersion (srcChartι k i) :=
  IsOpenImmersion.comp _ _

/-- The first component of the chart inclusion. -/
lemma srcChartι_fst (i : Fin 2) :
    srcChartι k i ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k)
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := chartRing k i) (B := L k)))
        ≫ chartObjHom k i := by
  rw [srcChartι, Category.assoc, srcChartMap_fst, ← Category.assoc]
  rw [srcChartIso_inv_fst k i]

 /-- The second component of the chart inclusion. -/
lemma srcChartι_snd (i : Fin 2) :
    srcChartι k i ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k)
      = Spec.map (CommRingCat.ofHom
          ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k i) (B := L k))))) := by
  rw [srcChartι, Category.assoc, srcChartMap_snd]
  rw [srcChartIso_inv_snd k i]

/-- The chart-level scaling morphism `D₊(Xᵢ) × 𝔾_m ⟶ ℙ¹`. -/
noncomputable abbrev srcChartHom (i : Fin 2) :
    Spec (CommRingCat.of (srcChartRing k i)) ⟶ (Work.AbVar.P1 k).left :=
  Spec.map (CommRingCat.ofHom (thetaRing k i)) ≫ chartObjHom k i

/-- The structure map of the chart `D₊(Xᵢ) × 𝔾_m`. -/
lemma srcChartHom_hom (i : Fin 2) :
    srcChartHom k i ≫ (Work.AbVar.P1 k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k (srcChartRing k i))) := by
  rw [srcChartHom, Category.assoc, chartObjHom_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  rw [RingHom.comp_apply, thetaRing_algebraMap]

end

end Work.AbVar.P1Action
