/-
# Naturality of the evaluation pairing `μ_T : ℤ[T] ⟶ ℤ■[T]`

This module records the *naturality in `T`* of the evaluation pairing of REFS/03 §4 in the form
needed by the Čech argument for the base case of AN5 (`Work.ANALYTIC.profinite_HI_pt`): there is a
functor `sd : LightProfinite ⥤ LightCondAb` with `sd.obj T ≅ ℤ■[T] = ihom (C(T,ℤ)_disc) 𝟙`
(`Work.ANALYTIC.solidDual T`), together with a natural transformation
`mu : ℤ[-] ⟹ sd.obj -` (`zmap f ≫ mu T = mu S ≫ sd.map f`) whose components are solid-equivalences.

## How this is proved

`Work.ANALYTIC.muT T : ℤ[T] ⟶ ℤ■[T]` (AN3, `Work.ANALYTIC.exists_muT`) is *chosen* by
`Classical.choose`, so it carries no naturality information.  What it does carry is solidity:
`Work.ANALYTIC.muT_solidEquiv : SolidEquiv ((single 0).map (muT T))`, i.e. for every `N : D(Solid)`

  `precomp (muT T) : Hom_D((single 0).obj ℤ■[T], iD N) ⟶ Hom_D((single 0).obj ℤ[T], iD N)`

is a bijection.  Specialising to `N = (single 0).obj ⟨ℤ■[T'], -⟩` and using

* the compatibility of `derivedInclusion` with `DerivedCategory.singleFunctor`
  (`Functor.mapDerivedCategorySingleFunctor`), and
* the full faithfulness of `(singleFunctor LightCondAb 0)` (Mathlib,
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`),

this bijection becomes the *abelian-category* statement

  `bijective_precomp_muT : Bijective (fun u : ℤ■[T] ⟶ ℤ■[T'] => muT T ≫ u)`.

Consequently `muT T ≫ -` is injective, which makes the choice of `sd.map f` in the square

  `zmap f ≫ muT T' = muT T ≫ sd.map f`

unique; so the maps `sd.map f` may be defined by `Classical.choose` and functoriality
(`map_id`, `map_comp`) follows from uniqueness.  This is the content of `Aux.sdFunctor`, and the
requested statement follows with `mu T := muT T`.
-/
import Mathlib
import Submission.Work.ANALYTIC.SolidDual
import Submission.Work.ANALYTIC.MuT
import Submission.Work.ANALYTIC.exists_kTilde
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ATOM.Main
import Submission.Work.TOOLKIT.Main
import Submission.Work.ANALYTIC.isSolid_ihom
import Submission.Work.ANALYTIC.CatAux.Basic
import Submission.Work.DISC.Main

namespace Work.ANALYTIC.CechPt

namespace Aux

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-! ## A pair of elementary transport lemmas for precomposition maps -/

/-- Precomposition with a fixed morphism is invariant under an isomorphism of its target. -/
private lemma bijective_precomp_target_iso_forward {C : Type*} [Category C] {X Y Z Z' : C}
    (f : X ⟶ Y) (e : Z ≅ Z')
    (h : Function.Bijective (fun g : Y ⟶ Z => f ≫ g)) :
    Function.Bijective (fun g : Y ⟶ Z' => f ≫ g) := by
  constructor
  · intro g₁ g₂ hg
    beta_reduce at hg
    have h1 : (f ≫ g₁) ≫ e.inv = (f ≫ g₂) ≫ e.inv := by rw [hg]
    simp only [Category.assoc] at h1
    have h2 := h.1 h1
    have h3 : (g₁ ≫ e.inv) ≫ e.hom = (g₂ ≫ e.inv) ≫ e.hom := by rw [h2]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h3
  · intro g
    obtain ⟨g₀, hg₀⟩ := h.2 (g ≫ e.inv)
    beta_reduce at hg₀
    refine ⟨g₀ ≫ e.hom, ?_⟩
    beta_reduce
    rw [← Category.assoc, hg₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Conjugation of precomposition along a fully faithful functor: if `F` is fully faithful and
precomposition with `F.map f` is bijective on `Hom(F.obj Y, F.obj Z)`, then precomposition with `f`
is bijective on `Hom(Y, Z)`. -/
private lemma bijective_precomp_of_fullyFaithful {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Faithful] [F.Full] {X Y Z : C} (f : X ⟶ Y)
    (h : Function.Bijective (fun g : F.obj Y ⟶ F.obj Z => F.map f ≫ g)) :
    Function.Bijective (fun u : Y ⟶ Z => f ≫ u) := by
  constructor
  · intro u₁ u₂ hu
    have hu' : F.map (f ≫ u₁) = F.map (f ≫ u₂) := congrArg F.map hu
    rw [Functor.map_comp, Functor.map_comp] at hu'
    exact F.map_injective (h.1 hu')
  · intro u
    obtain ⟨g, hg⟩ := h.2 (F.map u)
    beta_reduce at hg
    obtain ⟨v, hv⟩ := F.map_surjective g
    refine ⟨v, ?_⟩
    have h3 : F.map (f ≫ v) = F.map u := by rw [Functor.map_comp, hv, hg]
    exact F.map_injective h3

/-! ## The solid dual is a solid object -/

/-- `ℤ■[T] = ihom (C(T,ℤ)_disc) 𝟙` is solid: internal homs into a solid object are solid
(`Work.ANALYTIC.isSolid_ihom`) and the unit is the discrete `ℤ`
(`Work.ANALYTIC.unit_eq_Z`, `Work.DISC.isSolid_disc`). -/
theorem isSolid_solidDual (T : LightProfinite.{0}) : isSolid (Work.ANALYTIC.solidDual T) :=
  Work.ANALYTIC.isSolid_ihom (Work.ANALYTIC.Cdisc T) (𝟙_ LightCondAb)
    (by rw [Work.ANALYTIC.unit_eq_Z]; exact Work.DISC.isSolid_disc (ModuleCat.of ℤ ℤ))

/-! ## The key bijectivity: precomposition with `μ_T` into `ℤ■[T']` -/

/-- **The solidity of `μ_T`, read off in the abelian category.**  For light profinite `S`, `T`,
precomposition with `Work.ANALYTIC.muT S` is a bijection
`Hom(ℤ■[S], ℤ■[T]) → Hom(ℤ[S], ℤ■[T])`.

This is the degree-`0` part of `Work.ANALYTIC.muT_solidEquiv S` (`SolidEquiv` is defined as
bijectivity of precomposition on `Hom_D(-, derivedInclusion.obj N)`), transported from the derived
category to the abelian category by the full faithfulness of `singleFunctor LightCondAb 0`. -/
theorem bijective_precomp_muT (S T : LightProfinite.{0}) :
    Function.Bijective (fun u : Work.ANALYTIC.solidDual S ⟶ Work.ANALYTIC.solidDual T =>
      Work.ANALYTIC.muT S ≫ u) := by
  have hN := Work.ANALYTIC.muT_solidEquiv S
    ((DerivedCategory.singleFunctor Solid 0).obj
      ⟨Work.ANALYTIC.solidDual T, isSolid_solidDual T⟩)
  have heA : derivedInclusion.obj ((DerivedCategory.singleFunctor Solid 0).obj
      ⟨Work.ANALYTIC.solidDual T, isSolid_solidDual T⟩)
      ≅ (DerivedCategory.singleFunctor LightCondAb 0).obj (Work.ANALYTIC.solidDual T) :=
    (Functor.mapDerivedCategorySingleFunctor isSolid.ι (n := 0)).app
      ⟨Work.ANALYTIC.solidDual T, isSolid_solidDual T⟩
  have hN2 : Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb 0).obj (Work.ANALYTIC.solidDual S) ⟶
        (DerivedCategory.singleFunctor LightCondAb 0).obj (Work.ANALYTIC.solidDual T) =>
      (DerivedCategory.singleFunctor LightCondAb 0).map (Work.ANALYTIC.muT S) ≫ g) :=
    bijective_precomp_target_iso_forward
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ANALYTIC.muT S)) heA hN
  exact bijective_precomp_of_fullyFaithful (DerivedCategory.singleFunctor LightCondAb 0)
    (Work.ANALYTIC.muT S) hN2

/-! ## The functor `T ↦ ℤ■[T]` with `mu := muT` -/

/-- The structure maps of `T ↦ ℤ■[T]`: the unique `u` with `muT S ≫ u = zmap f ≫ muT T`
(existence and uniqueness are `bijective_precomp_muT S T`). -/
noncomputable def sdMap {S T : LightProfinite.{0}} (f : S ⟶ T) :
    Work.ANALYTIC.solidDual S ⟶ Work.ANALYTIC.solidDual T :=
  Classical.choose ((bijective_precomp_muT S T).2 (Work.ATOM.zmap f ≫ Work.ANALYTIC.muT T))

/-- The defining property of `sdMap`: naturality of `muT` along it. -/
theorem sdMap_spec {S T : LightProfinite.{0}} (f : S ⟶ T) :
    Work.ANALYTIC.muT S ≫ sdMap f = Work.ATOM.zmap f ≫ Work.ANALYTIC.muT T :=
  Classical.choose_spec ((bijective_precomp_muT S T).2 (Work.ATOM.zmap f ≫ Work.ANALYTIC.muT T))

theorem zmap_id (T : LightProfinite.{0}) : Work.ATOM.zmap (𝟙 T) = 𝟙 (Work.ATOM.zfree T) :=
  CategoryTheory.Functor.map_id (lightProfiniteToLightCondSet ⋙ free ℤ) T

theorem zmap_comp {S T U : LightProfinite.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    Work.ATOM.zmap (f ≫ g) = Work.ATOM.zmap f ≫ Work.ATOM.zmap g :=
  CategoryTheory.Functor.map_comp (lightProfiniteToLightCondSet ⋙ free ℤ) f g

/-- `T ↦ ℤ■[T]`, made functorial by the *uniqueness* in `bijective_precomp_muT`: both sides of
`map_comp` are preimages of `zmap (f ≫ g) ≫ muT U` under the injective map `muT S ≫ -`. -/
noncomputable def sdFunctor : LightProfinite.{0} ⥤ LightCondAb where
  obj T := Work.ANALYTIC.solidDual T
  map {_ _} f := sdMap f
  map_id T := by
    apply (bijective_precomp_muT T T).1
    beta_reduce
    rw [sdMap_spec, zmap_id]
    simp
  map_comp {S T U} f g := by
    apply (bijective_precomp_muT S U).1
    beta_reduce
    rw [sdMap_spec (f ≫ g)]
    calc Work.ATOM.zmap (f ≫ g) ≫ Work.ANALYTIC.muT U
        = (Work.ATOM.zmap f ≫ Work.ATOM.zmap g) ≫ Work.ANALYTIC.muT U := by rw [zmap_comp]
      _ = Work.ATOM.zmap f ≫ (Work.ATOM.zmap g ≫ Work.ANALYTIC.muT U) := Category.assoc _ _ _
      _ = Work.ATOM.zmap f ≫ (Work.ANALYTIC.muT T ≫ sdMap g) := by rw [sdMap_spec g]
      _ = (Work.ATOM.zmap f ≫ Work.ANALYTIC.muT T) ≫ sdMap g := (Category.assoc _ _ _).symm
      _ = (Work.ANALYTIC.muT S ≫ sdMap f) ≫ sdMap g := by rw [sdMap_spec f]
      _ = Work.ANALYTIC.muT S ≫ (sdMap f ≫ sdMap g) := Category.assoc _ _ _

end

end Aux

theorem solidFreeNaturalMu :
    ∃ (sd : CategoryTheory.Functor LightProfinite.{0} LightCondAb)
      (mu : ∀ T : LightProfinite.{0}, (LightCondensed.free (R := ℤ)).obj T.toCondensed ⟶ sd.obj T),
      (∀ T : LightProfinite.{0},
        Nonempty (CategoryTheory.Iso (sd.obj T) (Work.ANALYTIC.solidDual T))) ∧
      (∀ (S T : LightProfinite.{0}) (f : S ⟶ T),
        CategoryTheory.CategoryStruct.comp (Work.ATOM.zmap f) (mu T) =
          CategoryTheory.CategoryStruct.comp (mu S) (sd.map f)) ∧
      (∀ T : LightProfinite.{0}, Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map (mu T))) := by
  refine ⟨Aux.sdFunctor, fun T => Work.ANALYTIC.muT T, ?_, ?_, ?_⟩
  · intro T
    exact ⟨CategoryTheory.Iso.refl _⟩
  · intro S T f
    exact (Aux.sdMap_spec f).symm
  · intro T
    exact Work.ANALYTIC.muT_solidEquiv T

end Work.ANALYTIC.CechPt
