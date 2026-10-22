import Mathlib
import Submission.Work.ANALYTIC.RealSideDefs

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.regularTopology
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-!
# The sheaf `∏_ℕ ℝ` (the ℝ-valued analogue of `∏_ℕ ℤ`)

The presheaf `prodRealPresheaf` of `Submission/Work/ANALYTIC/RealSideDefs.lean` sends a light
profinite set `S` to the `ℤ`-module of `ℕ`-indexed families of continuous functions `S → ℝ`; it is
the model of `∏_ℕ ℝ` used in AN2 (REFS/03 §3).

Here we prove that it is a sheaf for the coherent (= regular + extensive) topology on
`LightProfinite`: it preserves finite products and satisfies the equalizer condition for effective
epimorphisms.  This is the exact ℝ-analogue of `Work.ANALYTIC.prodZPresheaf_sheaf`, with the same
route:

* currying of continuous maps identifies `prodRealPresheaf ⋙ forget (ModuleCat ℤ)` with the Yoneda
  presheaf of the topological space `ℕ → ℝ` (product topology),
* `PreservesFiniteProducts` and the equalizer condition are transported along that natural
  isomorphism; for the latter we use `equalizerCondition_yonedaPresheaf` together with the fact
  that effective epimorphisms of light profinite sets are surjective, hence quotient maps.
-/

/-- The presheaf `prodRealPresheaf`, with values in types (`forget (ModuleCat ℤ)`). -/
abbrev prodRealForget.{u} : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  prodRealPresheaf.{u} ⋙ CategoryTheory.forget (ModuleCat.{u, 0} ℤ)

/-- The Yoneda presheaf of the topological space `ℕ → ℝ` (product topology), restricted to light
profinite sets.  This is the "curried" model of `prodRealPresheaf`. -/
abbrev yonedaProdReal.{u} : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  ContinuousMap.yonedaPresheaf (LightProfinite.toTopCat : LightProfinite.{u} ⥤ TopCat.{u})
    (ℕ → ℝ)

/-- Currying of continuous maps: a family of continuous `ℝ`-valued functions is the same thing as a
continuous function into the product `ℕ → ℝ`. -/
noncomputable def prodRealIsoComp.{u} (S : LightProfinite.{u}ᵒᵖ) :
    prodRealForget.{u}.obj S ≅ yonedaProdReal.{u}.obj S :=
  Equiv.toIso (ContinuousMap.piEquiv ↥(S.unop) (fun _ : ℕ => ℝ))

/-- The natural isomorphism
`prodRealPresheaf ⋙ forget (ModuleCat ℤ) ≅ yonedaPresheaf toTopCat (ℕ → ℝ)`
given by currying; it is natural because currying commutes with precomposition. -/
noncomputable def prodRealIso.{u} : prodRealForget.{u} ≅ yonedaProdReal.{u} :=
  NatIso.ofComponents (fun S => prodRealIsoComp S) (fun {S T} f => by
    ext x
    show ContinuousMap.pi (prodRealForget.map f x) =
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

/-- `prodRealForget` preserves finite products, transported from `yonedaProdReal`. -/
theorem preservesFiniteProducts_prodRealForget.{u} : PreservesFiniteProducts (prodRealForget.{u}) := by
  haveI : PreservesFiniteProducts (yonedaProdReal.{u}) := inferInstance
  exact preservesFiniteProducts_of_natIso' (prodRealIso.{u}).symm

/-- `prodRealForget` satisfies the equalizer condition, transported from `yonedaProdReal`. -/
theorem equalizerCondition_prodRealForget.{u} : EqualizerCondition (prodRealForget.{u}) := by
  have hY2 : EqualizerCondition (yonedaProdReal.{u}) := by
    haveI : ∀ (Z B : LightProfinite.{u}) (π : Z ⟶ B) [EffectiveEpi π],
        PreservesLimit (cospan π π) (LightProfinite.toTopCat.{u}) :=
      fun _ _ _ _ => inferInstance
    refine equalizerCondition_yonedaPresheaf (LightProfinite.toTopCat.{u}) (ℕ → ℝ) ?_
    intro Z B π _
    exact Topology.IsQuotientMap.of_surjective_continuous
      ((LightProfinite.effectiveEpi_iff_surjective π).mp ‹EffectiveEpi π›) π.hom.hom.continuous
  exact equalizerCondition_of_natIso' (prodRealIso.{u}).symm hY2

/-- **The presheaf `S ↦ (ℕ → C(S,ℝ))` of `ℕ`-indexed families of continuous real-valued functions
on a light profinite set is a sheaf**: it preserves finite products and satisfies the equalizer
condition for the regular topology.

Route: the composite `prodRealPresheaf ⋙ forget (ModuleCat ℤ)` is naturally isomorphic (by currying
of continuous maps) to the Yoneda presheaf
`ContinuousMap.yonedaPresheaf LightProfinite.toTopCat (ℕ → ℝ)` of the topological space `ℕ → ℝ`
with the product topology.  Transport the sheaf conditions along that natural isomorphism:
`PreservesFiniteProducts` by transport along a natural iso, and the equalizer condition via
`CategoryTheory.regularTopology.equalizerCondition_of_natIso` together with
`equalizerCondition_yonedaPresheaf` (using `Topology.IsQuotientMap.of_surjective_continuous` for
effective epimorphisms in `LightProfinite`, `LightProfinite.effectiveEpi_iff_surjective`). -/
theorem prodReal_sheaf : CategoryTheory.Limits.PreservesFiniteProducts (CategoryTheory.Functor.comp Work.ANALYTIC.prodRealPresheaf (CategoryTheory.forget (ModuleCat ℤ))) ∧ CategoryTheory.regularTopology.EqualizerCondition (CategoryTheory.Functor.comp Work.ANALYTIC.prodRealPresheaf (CategoryTheory.forget (ModuleCat ℤ))) :=
  ⟨preservesFiniteProducts_prodRealForget, equalizerCondition_prodRealForget⟩

end Work.ANALYTIC
