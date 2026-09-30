import Mathlib
import Submission.Work.AbVar.P1Action.SourceChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
The range of the chart inclusion `srcChartι k i : Spec (chartRing k i ⊗[k] k[T;T⁻¹]) ⟶ ℙ¹ × 𝔾_m`
is the preimage, under the first projection `ℙ¹ × 𝔾_m ⟶ ℙ¹`, of the standard affine chart
`D₊(Xᵢ) ⊆ ℙ¹`.

The proof is a pullback-range computation: the chart inclusion is the inverse of the
identification `srcChartIso` followed by the pullback map `srcChartMap`, which sits in the
pullback square

```
  srcChartScheme k i --fst--> Spec (chartRing k i)
        |                              |
   srcChartMap                   chartObjHom
        v                              v
    srcScheme k ---------fst------> ℙ¹
```

and the range of a pullback map along an open immersion is the preimage of the range.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

/-- The square computing `srcChartMap k i` as the pullback of `chartObjHom k i` along `fst` is a
pullback square. -/
lemma srcChartMap_isPullback (k : Type*) [Field k] (i : Fin 2) :
    IsPullback (pullback.fst (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k))
      (srcChartMap k i) (chartObjHom k i) (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)) := by
  have hb : IsPullback (pullback.fst (Work.AbVar.P1 k).hom (gmHom k))
      (pullback.snd (Work.AbVar.P1 k).hom (gmHom k)) (Work.AbVar.P1 k).hom (gmHom k) :=
    IsPullback.of_hasPullback _ _
  have comm : pullback.fst (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k) ≫ chartObjHom k i
      = srcChartMap k i ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k) :=
    (srcChartMap_fst k i).symm
  have hout : IsPullback (pullback.fst (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k))
      (srcChartMap k i ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k))
      (chartObjHom k i ≫ (Work.AbVar.P1 k).hom) (gmHom k) := by
    rw [srcChartMap_snd]
    exact IsPullback.of_hasPullback _ _
  exact (IsPullback.paste_vert_iff hb comm).mp hout

/-- The range of the pullback map `srcChartMap k i` is the preimage of the range of
`chartObjHom k i` under `fst`. -/
lemma srcChartMap_opensRange_aux (k : Type*) [Field k] (i : Fin 2) :
    (srcChartMap k i).opensRange
      = (pullback.fst (Work.AbVar.P1 k).hom (gmHom k)) ⁻¹ᵁ (chartObjHom k i).opensRange := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (srcChartMap_isPullback k i) ⊤
  simpa [Scheme.Hom.image_top_eq_opensRange] using h

/-- The range of the chart inclusion `srcChartι k i` is the preimage of `D₊(Xᵢ)` along `fst`. -/
theorem srcChart_range (k : Type*) [Field k] (i : Fin 2) :
    (Work.AbVar.P1Action.srcChartι k i).opensRange
      = (TopologicalSpace.Opens.map (CategoryTheory.Limits.pullback.fst (Work.AbVar.P1 k).hom
          (Work.AbVar.P1Action.gmHom k)).base).obj
          (AlgebraicGeometry.Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)) := by
  have h1 : (srcChartι k i).opensRange = (srcChartMap k i).opensRange :=
    Scheme.Hom.opensRange_comp_of_isIso (srcChartIso k i).inv (srcChartMap k i)
  have hb : (chartObjHom k i).opensRange
      = Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i) :=
    Proj.opensRange_awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)
      (Work.AbVar.ProjectiveLine.X_mem_stdG i) (by norm_num)
  rw [h1, srcChartMap_opensRange_aux k i, hb]

end Work.AbVar.P1Action
