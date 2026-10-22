import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.Cofibrant

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

noncomputable section

/-!
# `CWIND/T13`: derived solidification of the singular chain complex

The complex of integral singular chains of a space is degreewise discrete, hence degreewise solid.
Writing `η` for the unit of the solidification adjunction `sol ⊣ ι`, this gives a natural isomorphism
`ηC : 𝟭 ⟶ solC ⋙ ιC` of complexes that is an isomorphism at every complex `C_sing(X)`.  Combining
this with the counit comparison `D.α : Q ⋙ L ⟶ solC ⋙ Q` of the derived solidification (an
isomorphism at solid-cofibrant complexes) and with `derivedInclusionFactors : Q ⋙ ι_D ≅ ιC ⋙ Q`
produces the natural isomorphism `ι_D (L (Q C_sing X)) ≅ Q C_sing X`.
-/

/-! ## Auxiliary lemmas -/

/-- `isSolid` is invariant under isomorphism. -/
lemma isSolid_of_iso {A B : LightCondAb} (h : isSolid A) (e : A ≅ B) : isSolid B := by
  rw [isSolid] at h ⊢
  exact (NatTrans.isIso_app_iff_of_iso (MonoidalClosed.pre oneMinusShift) e).mp h

/-- The complex of integral singular chains of `X` with discrete light condensed coefficients,
before extending the homological indexing to `ℤ`. -/
abbrev singChainComplexLightCondAux (X : TopCat.{0}) : ChainComplex LightCondAb ℕ :=
  ((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)

/-- Every term of the singular chain complex of `X` is a discrete light condensed abelian group,
and therefore solid. -/
lemma isSolid_singularChains_X (hDisc : DiscProp) (X : TopCat.{0}) (n : ℤ) :
    isSolid ((singularChainsLightCondAbComplexFunctor.obj X).X n) := by
  by_cases hn : n ≤ 0
  · have h : ComplexShape.embeddingDownNat.f ((-n).toNat) = n := by
      rw [ComplexShape.embeddingDownNat_f]; omega
    refine isSolid_of_iso (hDisc.1 ((((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X ((-n).toNat))) ?_
    exact ((singChainComplexLightCondAux X).extendXIso ComplexShape.embeddingDownNat h).symm
  · have hn' : 0 < n := by omega
    rw [isSolid]
    have hzero : IsZero ((singularChainsLightCondAbComplexFunctor.obj X).X n) :=
      HomologicalComplex.isZero_extend_X (singChainComplexLightCondAux X)
        ComplexShape.embeddingDownNat n (by
          intro m hm
          simp only [ComplexShape.embeddingDownNat_f] at hm
          omega)
    have hz : IsZero ((ihom P).obj ((singularChainsLightCondAbComplexFunctor.obj X).X n)) :=
      (ihom P).map_isZero hzero
    have h : (MonoidalClosed.pre oneMinusShift).app
        ((singularChainsLightCondAbComplexFunctor.obj X).X n) = (hz.iso hz).hom := hz.eq_of_src _ _
    rw [h]
    infer_instance

section SolidificationUnit

variable [isSolid.ι.IsRightAdjoint]

/-- The unit `η` of the solidification adjunction `sol ⊣ ι`, applied degreewise to complexes:
a natural transformation `𝟭 ⟶ solC ⋙ ιC`. -/
abbrev solUnitC : 𝟭 (CochainComplex LightCondAb ℤ) ⟶ solC ⋙ ιC :=
  NatTrans.mapHomologicalComplex solAdj.unit (ComplexShape.up ℤ)

/-- The degreewise unit of the solidification adjunction is an isomorphism at any complex all of
whose terms are solid. -/
lemma isIso_solUnitC_app (C : CochainComplex LightCondAb ℤ) (hC : ∀ n, isSolid (C.X n)) :
    IsIso (solUnitC.app C) := by
  haveI : ∀ n : ℤ, IsIso ((solUnitC.app C).f n) := fun n => by
    change IsIso (solAdj.unit.app (C.X n))
    haveI : IsIso (solAdj.unit.app (isSolid.ι.obj ⟨C.X n, hC n⟩)) := inferInstance
    exact this
  exact HomologicalComplex.Hom.isIso_of_components (solUnitC.app C)

end SolidificationUnit

/-! ## The main theorem -/

/-- **CWIND/T13.**  For every space `X` there is a natural isomorphism
`ι_D (L (Q C_sing(X))) ≅ Q C_sing(X)`: after derived solidification, the (discrete) singular chain
complex is unchanged.  Since `C_sing(X)` is solid-cofibrant (`hC`), the counit
`D.α : L (Q C) ⟶ Q (solC C)` of the derived solidification is an isomorphism there
(`DerivedPackage.iso_of_cofibrant`); `C_sing(X)` is degreewise discrete, hence degreewise solid, and
the counit `sol ∘ ι ⟶ 𝟭` of the solidification adjunction is an isomorphism, so `solC C ≅ C`; and
the derived inclusion factors as `Q ∘ ιC` (`derivedInclusionFactors`). -/
theorem iso_solDerivedInclusion (hD : DerivedProp) [isSolid.ι.IsRightAdjoint] (D : DerivedPackage)
    (hDisc : DiscProp)
    (hC : ∀ X : TopCat.{0}, SolidCofibrant (singularChainsLightCondAbComplexFunctor.obj X)) :
    Nonempty ((singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q ⋙ D.L ⋙ derivedInclusion) ≅
      (singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q)) := by
  -- abbreviations for the functors involved
  let Kl : TopCat.{0} ⥤ CochainComplex LightCondAb ℤ := singularChainsLightCondAbComplexFunctor
  let Ql : CochainComplex LightCondAb ℤ ⥤ DLightCondAb := DerivedCategory.Q
  let Qs : CochainComplex Solid ℤ ⥤ DSolid := DerivedCategory.Q
  let Rf : DSolid ⥤ DLightCondAb := derivedInclusion
  -- the comparison `D.α` is an isomorphism, since `C_sing(X)` is solid-cofibrant
  haveI hαW : ∀ X : TopCat.{0},
      IsIso ((Functor.whiskerRight (Functor.whiskerLeft Kl D.α) Rf).app X) := by
    intro X
    simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
    haveI : IsIso (D.α.app (Kl.obj X)) := D.iso_of_cofibrant _ (hC X)
    infer_instance
  haveI hαW' : IsIso (Functor.whiskerRight (Functor.whiskerLeft Kl D.α) Rf) :=
    NatIso.isIso_of_isIso_app _
  -- the degreewise unit of the solidification adjunction is an isomorphism on `C_sing(X)`
  haveI hηC : ∀ X : TopCat.{0}, IsIso (solUnitC.app (Kl.obj X)) := fun X =>
    isIso_solUnitC_app (Kl.obj X) (fun n => isSolid_singularChains_X hDisc X n)
  haveI hηW : ∀ X : TopCat.{0},
      IsIso ((Functor.whiskerRight (Functor.whiskerLeft Kl solUnitC) Ql).app X) := by
    intro X
    simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  haveI hηW' : IsIso (Functor.whiskerRight (Functor.whiskerLeft Kl solUnitC) Ql) :=
    NatIso.isIso_of_isIso_app _
  -- the three pieces of the natural isomorphism
  let Eη : (Kl ⋙ Ql) ≅ ((Kl ⋙ solC) ⋙ (ιC ⋙ Ql)) :=
    asIso (Functor.whiskerRight (Functor.whiskerLeft Kl solUnitC) Ql)
  let Eα : (Kl ⋙ Ql ⋙ D.L ⋙ Rf) ≅ ((Kl ⋙ solC) ⋙ (Qs ⋙ Rf)) :=
    asIso (Functor.whiskerRight (Functor.whiskerLeft Kl D.α) Rf)
  let Ef : ((Kl ⋙ solC) ⋙ (Qs ⋙ Rf)) ≅ ((Kl ⋙ solC) ⋙ (ιC ⋙ Ql)) :=
    Functor.isoWhiskerLeft (Kl ⋙ solC) isSolid.ι.mapDerivedCategoryFactors
  exact ⟨Eα ≪≫ Ef ≪≫ Eη.symm⟩

end

end Work.CWIND.Cofibrant
