import Submission.Work.CWIND.GClass.GG_preserves_mono

/-!
# The functor `GG` preserves pushouts

`GG` is the composite of the degreewise discretisation functor
`(LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (down ℕ)` (which preserves colimits,
being a left adjoint composed with `mapHomologicalComplex`) and the extension-by-zero functor
`ComplexShape.embeddingDownNat.extendFunctor LightCondAb`.

Extension by zero preserves pushouts: for each cochain degree `q`, the functor
`extendFunctor ⋙ eval _ _ q` is either (if `q = -n` is in the image of the embedding) isomorphic
to `eval _ _ n`, hence preserves colimits, or (if `q > 0`) takes values in zero objects only, in
which case the image cocone over a diagram of zero objects with zero point is a colimit cocone.
Colimits of complexes are computed degreewise (`HomologicalComplex.preservesColimitsOfShape_of_eval`),
which gives the result.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

/-- A cocone over a diagram of zero objects, whose point is a zero object, is a colimit cocone. -/
def isColimit_of_isZero {J : Type*} [Category* J] {C : Type*} [Category* C]
    [HasZeroMorphisms C] {F : J ⥤ C} (c : Cocone F) (hpt : IsZero c.pt)
    (hF : ∀ j, IsZero (F.obj j)) : IsColimit c where
  desc := fun s => hpt.to_ s.pt
  fac := fun s j => (hF j).eq_of_src _ _
  uniq := fun s m _ => hpt.eq_of_src _ _

/-- Extension by zero along `ComplexShape.embeddingDownNat` preserves colimits of the shape of
spans, i.e. pushouts. -/
instance instPreservesColimitsOfShapeExtendFunctorGClass :
    PreservesColimitsOfShape WalkingSpan
      (ComplexShape.embeddingDownNat.extendFunctor LightCondAb) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun q => by
    by_cases hq : ∃ n : ℕ, (ComplexShape.embeddingDownNat.f n : ℤ) = q
    · obtain ⟨n, hn⟩ := hq
      haveI : PreservesColimitsOfShape WalkingSpan
          (HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) n) := inferInstance
      exact CategoryTheory.Limits.preservesColimitsOfShape_of_natIso
        (ComplexShape.Embedding.extendFunctorCompEvalIso LightCondAb
          (e := ComplexShape.embeddingDownNat) hn).symm
    · have hq' : ∀ n : ℕ, (ComplexShape.embeddingDownNat.f n : ℤ) ≠ q := fun n hn => hq ⟨n, hn⟩
      exact ⟨fun {K} => ⟨fun {c} _ => ⟨isColimit_of_isZero _
        (HomologicalComplex.isZero_extend_X c.pt ComplexShape.embeddingDownNat q hq')
        (fun j => HomologicalComplex.isZero_extend_X (K.obj j) ComplexShape.embeddingDownNat q
          hq')⟩⟩⟩)

/-- `GG` preserves pushouts. -/
theorem GG_preserves_pushout {W X Y Z : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (hp : IsPushout f g h i) :
    IsPushout (GG.map f) (GG.map g) (GG.map h) (GG.map i) := by
  let F₁ := (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)
  let F₂ := ComplexShape.embeddingDownNat.extendFunctor LightCondAb
  have hL : (LightCondensed.discrete (ModuleCat ℤ)).IsLeftAdjoint :=
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).isLeftAdjoint
  haveI : (LightCondensed.discrete (ModuleCat ℤ)).IsLeftAdjoint := hL
  have hsh₁ : PreservesColimitsOfShape WalkingSpan F₁ := inferInstance
  haveI : PreservesColimitsOfShape WalkingSpan F₁ := hsh₁
  haveI hp₁ : PreservesColimit (span f g) F₁ := hsh₁.preservesColimit (K := span f g)
  have h₁ := Functor.map_isPushout F₁ hp
  have hsh₂ : PreservesColimitsOfShape WalkingSpan F₂ :=
    instPreservesColimitsOfShapeExtendFunctorGClass
  haveI hp₂ : PreservesColimit (span (F₁.map f) (F₁.map g)) F₂ :=
    hsh₂.preservesColimit (K := span (F₁.map f) (F₁.map g))
  have h₂ := Functor.map_isPushout F₂ h₁
  simpa [GG, F₁, F₂, Functor.comp_map] using h₂

end Work.CWIND.GClass
