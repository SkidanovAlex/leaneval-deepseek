import Mathlib
import Submission.Work.ANALYTIC.ProdZ

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.regularTopology

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The presheaf `prodZPresheaf`, with values in types (`forget (ModuleCat ℤ)`). -/
abbrev prodZForget.{u} : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  prodZPresheaf.{u} ⋙ CategoryTheory.forget (ModuleCat.{u, 0} ℤ)

/-- The Yoneda presheaf of the topological space `ℕ → ℤ` (product topology), restricted to light
profinite sets.  This is the "curried" model of `prodZPresheaf`. -/
abbrev yonedaProdZ.{u} : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  ContinuousMap.yonedaPresheaf (LightProfinite.toTopCat : LightProfinite.{u} ⥤ TopCat.{u}) (ℕ → ℤ)

/-- Currying of continuous maps: a family of continuous `ℤ`-valued functions is the same thing as a
continuous function into the product `ℕ → ℤ`. -/
noncomputable def prodZIsoComp.{u} (S : LightProfinite.{u}ᵒᵖ) :
    prodZForget.{u}.obj S ≅ yonedaProdZ.{u}.obj S :=
  Equiv.toIso (ContinuousMap.piEquiv ↥(S.unop) (fun _ : ℕ => ℤ))

/-- The natural isomorphism `prodZPresheaf ⋙ forget (ModuleCat ℤ) ≅ yonedaPresheaf toTopCat (ℕ → ℤ)`
given by currying; it is natural because currying commutes with precomposition. -/
noncomputable def prodZIso.{u} : prodZForget.{u} ≅ yonedaProdZ.{u} :=
  NatIso.ofComponents (fun S => prodZIsoComp S) (fun {S T} f => by
    ext x
    show ContinuousMap.pi (prodZForget.map f x) =
      (ContinuousMap.pi x).comp (LightProfinite.toTopCat.map f.unop).hom
    ext s n
    rfl)

/-- Precomposition of finite products is a finite product (transporting `PreservesFiniteProducts`
along a natural isomorphism). -/
theorem preservesFiniteProducts_of_natIso' {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) [PreservesFiniteProducts F] : PreservesFiniteProducts G where
  preserves _ := preservesLimitsOfShape_of_natIso e

/-- The equalizer condition transports along a natural isomorphism. -/
theorem equalizerCondition_of_natIso' {C D : Type*} [Category* C] [Category* D] {P P' : Cᵒᵖ ⥤ D}
    (i : P ≅ P') (h : EqualizerCondition P) : EqualizerCondition P' :=
  equalizerCondition_of_natIso i h

/-- `prodZForget` preserves finite products, transported from `yonedaProdZ`. -/
theorem preservesFiniteProducts_prodZForget.{u} : PreservesFiniteProducts (prodZForget.{u}) := by
  haveI : PreservesFiniteProducts (yonedaProdZ.{u}) := inferInstance
  exact preservesFiniteProducts_of_natIso' (prodZIso.{u}).symm

/-- `prodZForget` satisfies the equalizer condition, transported from `yonedaProdZ`. -/
theorem equalizerCondition_prodZForget.{u} : EqualizerCondition (prodZForget.{u}) := by
  have hY2 : EqualizerCondition (yonedaProdZ.{u}) := by
    haveI : ∀ (Z B : LightProfinite.{u}) (π : Z ⟶ B) [EffectiveEpi π],
        PreservesLimit (cospan π π) (LightProfinite.toTopCat.{u}) :=
      fun _ _ _ _ => inferInstance
    refine equalizerCondition_yonedaPresheaf (LightProfinite.toTopCat.{u}) (ℕ → ℤ) ?_
    intro Z B π _
    exact Topology.IsQuotientMap.of_surjective_continuous
      ((LightProfinite.effectiveEpi_iff_surjective π).mp ‹EffectiveEpi π›) π.hom.hom.continuous
  exact equalizerCondition_of_natIso' (prodZIso.{u}).symm hY2

/-- The presheaf `prodZPresheaf` (`Submission/Work/ANALYTIC/ProdZ.lean`) of `ℕ`-indexed families of
continuous `ℤ`-valued functions is a sheaf: it preserves finite products and satisfies the equalizer
condition.  Hence `LightCondensed.ofSheafForgetLightProfinite prodZPresheaf _` is the light
condensed abelian group `∏_ℕ ℤ` with `boundedSeqSet S` as a submodule of its `S`-points, so that
the inclusion `∏^bnd ℤ ⊆ ∏ℤ` of AN2 is the identity on families.

Route: the composite `prodZPresheaf ⋙ forget (ModuleCat ℤ)` is naturally isomorphic (by currying of
continuous maps) to the Yoneda presheaf `ContinuousMap.yonedaPresheaf LightProfinite.toTopCat (ℕ → ℤ)`
of the topological space `ℕ → ℤ` with the product topology.  Transport the sheaf conditions along
that natural isomorphism: `PreservesFiniteProducts` by transport along a natural iso, and the
equalizer condition via `CategoryTheory.regularTopology.equalizerCondition_of_natIso` together with
`equalizerCondition_yonedaPresheaf` (using `Topology.IsQuotientMap.of_surjective_continuous` for
effective epimorphisms in `LightProfinite`, `LightProfinite.effectiveEpi_iff_surjective`). -/
theorem prodZPresheaf_sheaf :
    PreservesFiniteProducts (prodZPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) ∧
      EqualizerCondition (prodZPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
  ⟨preservesFiniteProducts_prodZForget, equalizerCondition_prodZForget⟩

end

end Work.ANALYTIC
