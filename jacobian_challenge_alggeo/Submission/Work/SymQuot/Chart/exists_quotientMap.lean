/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient map `X ⟶ X/Γ` (area SY)

For a scheme `X` with an action of a finite group `Γ` and a `Γ`-invariant affine open cover
(`Work.SymQuot.QuotientData`), the quotient `X/Γ` is built as the locally directed colimit of the
charts `chart U = Spec Γ(X,U)^Γ` (`Submission.Work.SymQuot.Quotient`).  This file constructs the
*quotient map*

`exists_quotientMap D : ∃ q : X ⟶ D.Quotient, (∀ U, U.ι ≫ q = chartMap U ≫ chartι U) ∧
  D.action.IsInvariantMorphism q ∧ Function.Surjective q`,

i.e. the morphism from `X` to the quotient which on each chart `U` of the cover is the chart map
`U ⟶ chart U` followed by the open immersion `chart U ⟶ X/Γ`.  It is `Γ`-invariant and surjective.

The map is obtained by gluing the local maps `chartMap U ≫ chartι U` over the open cover of `X` by
the invariant affine opens (`Scheme.Cover.glueMorphisms`); the compatibility on the overlaps is
`chartRes_chartMap` together with the fact that the pullback of two inclusions of open subschemes
is the inclusion of the intersection.  Invariance uses that the chart map is invariant under the
action of `Γ` on `U` (`resLE_chartMap`), and surjectivity uses that the charts cover the colimit
and that the chart maps of affine opens are surjective.
-/
import Mathlib
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Chart.chartRes_chartMap
import Submission.Work.SymQuot.Chart.chartFunctor_isLocallyDirected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Chart

/-- The pullback of the two inclusions `U.ι : U ⟶ X` and `V.ι : V ⟶ X` of open subschemes of `X`
is (isomorphic to) the intersection `U ⊓ V`, through the two inclusions `X.homOfLE inf_le_left` and
`X.homOfLE inf_le_right`: this is the inverse direction of `isPullback_opens_inf`. -/
private theorem lift_pullback_opens_aux {X : AlgebraicGeometry.Scheme} (U V : X.Opens) :
    ∃ e : CategoryTheory.Limits.pullback U.ι V.ι ⟶ (U ⊓ V).toScheme,
      CategoryTheory.CategoryStruct.comp e (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) =
        CategoryTheory.Limits.pullback.fst U.ι V.ι ∧
      CategoryTheory.CategoryStruct.comp e (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) =
        CategoryTheory.Limits.pullback.snd U.ι V.ι :=
  ⟨(AlgebraicGeometry.isPullback_opens_inf U V).isoPullback.inv,
    (AlgebraicGeometry.isPullback_opens_inf U V).isoPullback_inv_fst,
    (AlgebraicGeometry.isPullback_opens_inf U V).isoPullback_inv_snd⟩

/-- The chart map `U ⟶ chart U = Spec Γ(X,U)^Γ` of an invariant open is invariant under the action
of `Γ` on `U`: it factors through the invariants, on which the action is trivial.  Hence it
descends to the quotient `U/Γ` (i.e. it is the local model of the quotient map). -/
private theorem resLE_chartMap_aux {G : Type*} [Group G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {U : X.Opens} (hU : A.IsInvariantOpen U) (g : G) :
    CategoryTheory.CategoryStruct.comp ((A.hom g).resLE U U (le_of_eq (hU g).symm))
        (A.chartMap U hU) = A.chartMap U hU := by
  have hsub : (A.sectionHom U hU g).comp
      (Subring.subtype (Work.SymQuot.GAction.invariants A U hU)) =
      Subring.subtype (Work.SymQuot.GAction.invariants A U hU) := by
    apply RingHom.ext
    intro s
    have h := (Work.SymQuot.GAction.mem_invariants_iff A hU (s : Γ(X, U))).mp s.2 g⁻¹
    simpa using h
  have happ : CommRingCat.ofHom (Subring.subtype (Work.SymQuot.GAction.invariants A U hU)) ≫
      (A.hom g).appLE U U (le_of_eq (hU g).symm) =
      CommRingCat.ofHom (Subring.subtype (Work.SymQuot.GAction.invariants A U hU)) := by
    rw [show (A.hom g).appLE U U (le_of_eq (hU g).symm) =
      CommRingCat.ofHom (A.sectionHom U hU g) from rfl]
    rw [← CommRingCat.ofHom_comp, hsub]
  rw [Work.SymQuot.GAction.chartMap, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE (A.hom g) U U (le_of_eq (hU g).symm), Category.assoc,
    ← Spec.map_comp, happ, ← Work.SymQuot.GAction.chartMap]

/-- **Existence of the quotient map.**  For a scheme `X` with an action of a finite group `Γ`
together with a `Γ`-invariant affine open cover (`D : QuotientData Γ X`), there is a morphism
`q : X ⟶ D.Quotient` to the quotient which on every chart `U` of the cover restricts to
`chartMap U ≫ chartι U`.  Moreover `q` is `Γ`-invariant and surjective. -/
theorem exists_quotientMap {Γ : Type*} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme}
    (D : Work.SymQuot.QuotientData Γ X) :
    ∃ q : X ⟶ D.Quotient,
      (∀ U : D.Chart,
        CategoryTheory.CategoryStruct.comp U.1.ι q =
          CategoryTheory.CategoryStruct.comp (D.action.chartMap U.1 U.2.2) (D.chartι U)) ∧
      D.action.IsInvariantMorphism q ∧ Function.Surjective q := by
  -- The open cover of `X` by the invariant affine opens of the quotient data.
  let 𝒰 : X.OpenCover := {
    I₀ := D.Chart
    X := fun U => U.1.toScheme
    f := fun U => U.1.ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, fun i => inferInstance⟩
      obtain ⟨U, hUa, hUi, hxU⟩ := D.covers x
      exact ⟨⟨U, hUa, hUi⟩, ⟨x, hxU⟩, rfl⟩
  }
  -- The cocone property of the open immersions of the charts into the quotient.
  have chartRes_chartι : ∀ {W U : D.Chart} (h : W.1 ≤ U.1),
      D.action.chartRes W.1 U.1 h U.2.2 W.2.2 ≫ D.chartι U = D.chartι W := by
    intro W U h
    exact colimit.w D.chartFunctor (homOfLE h : W ⟶ U)
  -- The local maps `chartMap U ≫ chartι U` restrict along `W ≤ U` as `chartMap W ≫ chartι W`.
  have homOfLE_chartMap_chartι : ∀ {W U : D.Chart} (h : W.1 ≤ U.1),
      X.homOfLE h ≫ (D.action.chartMap U.1 U.2.2 ≫ D.chartι U) =
        D.action.chartMap W.1 W.2.2 ≫ D.chartι W := by
    intro W U h
    rw [← Category.assoc, Work.SymQuot.Chart.chartRes_chartMap D.action h U.2.2 W.2.2,
      Category.assoc, chartRes_chartι (W := W) (U := U) h]
  -- The compatibility of the local maps on the intersections of the charts.
  have keygen : ∀ {W U V : D.Chart} (hWU : W.1 ≤ U.1) (hWV : W.1 ≤ V.1)
      (e : CategoryTheory.Limits.pullback U.1.ι V.1.ι ⟶ W.1.toScheme)
      (he₁ : e ≫ X.homOfLE hWU = CategoryTheory.Limits.pullback.fst U.1.ι V.1.ι)
      (he₂ : e ≫ X.homOfLE hWV = CategoryTheory.Limits.pullback.snd U.1.ι V.1.ι),
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst U.1.ι V.1.ι)
        (CategoryTheory.CategoryStruct.comp (D.action.chartMap U.1 U.2.2) (D.chartι U)) =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd U.1.ι V.1.ι)
        (CategoryTheory.CategoryStruct.comp (D.action.chartMap V.1 V.2.2) (D.chartι V)) := by
    intro W U V hWU hWV e he₁ he₂
    have key₁ : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst U.1.ι V.1.ι)
        (CategoryTheory.CategoryStruct.comp (D.action.chartMap U.1 U.2.2) (D.chartι U)) =
        CategoryTheory.CategoryStruct.comp e
          (CategoryTheory.CategoryStruct.comp (D.action.chartMap W.1 W.2.2) (D.chartι W)) := by
      rw [← he₁, Category.assoc e (X.homOfLE hWU)
            (CategoryTheory.CategoryStruct.comp (D.action.chartMap U.1 U.2.2) (D.chartι U))]
      rw [homOfLE_chartMap_chartι (W := W) (U := U) hWU]
    have key₂ : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd U.1.ι V.1.ι)
        (CategoryTheory.CategoryStruct.comp (D.action.chartMap V.1 V.2.2) (D.chartι V)) =
        CategoryTheory.CategoryStruct.comp e
          (CategoryTheory.CategoryStruct.comp (D.action.chartMap W.1 W.2.2) (D.chartι W)) := by
      rw [← he₂, Category.assoc e (X.homOfLE hWV)
            (CategoryTheory.CategoryStruct.comp (D.action.chartMap V.1 V.2.2) (D.chartι V))]
      rw [homOfLE_chartMap_chartι (W := W) (U := V) hWV]
    rw [key₁, key₂]
  have compat : ∀ U V : D.Chart,
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst U.1.ι V.1.ι)
        (CategoryTheory.CategoryStruct.comp (D.action.chartMap U.1 U.2.2) (D.chartι U)) =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd U.1.ι V.1.ι)
        (CategoryTheory.CategoryStruct.comp (D.action.chartMap V.1 V.2.2) (D.chartι V)) := by
    intro U V
    obtain ⟨e, he₁, he₂⟩ := lift_pullback_opens_aux U.1 V.1
    exact keygen (W := D.inf U V) (U := U) (V := V)
      (inf_le_left : (D.inf U V).1 ≤ U.1) (inf_le_right : (D.inf U V).1 ≤ V.1) e he₁ he₂
  -- The quotient map, obtained by gluing the local maps.
  let q : X ⟶ D.Quotient :=
    𝒰.glueMorphisms (fun U => D.action.chartMap U.1 U.2.2 ≫ D.chartι U) (fun U V => compat U V)
  have hq : ∀ U : D.Chart, U.1.ι ≫ q = D.action.chartMap U.1 U.2.2 ≫ D.chartι U :=
    fun U => 𝒰.ι_glueMorphisms _ _ U
  refine ⟨q, hq, ?_, ?_⟩
  · -- `q` is invariant: on each chart it is `chartMap U ≫ chartι U`, which is invariant.
    intro g
    refine 𝒰.hom_ext _ _ (fun U => ?_)
    have hres : (D.action.hom g).resLE U.1 U.1 (le_of_eq (U.2.2 g).symm) ≫ U.1.ι =
        U.1.ι ≫ D.action.hom g :=
      Scheme.Hom.resLE_comp_ι _ _
    rw [← Category.assoc, ← hres, Category.assoc, hq U, ← Category.assoc,
      resLE_chartMap_aux D.action U.2.2 g, ← hq U]
  · -- `q` is surjective: the charts cover the quotient and the chart maps are surjective.
    intro y
    obtain ⟨U, x, hx⟩ := D.chartι_jointly_surjective y
    obtain ⟨x', hx'⟩ := Work.SymQuot.Chart.chartMap_surjective_of_affine D.action U.2.1 U.2.2 x
    refine ⟨U.1.ι x', ?_⟩
    have h := congrArg (fun f : U.1.toScheme ⟶ D.Quotient => f x') (hq U)
    simp only [Scheme.Hom.comp_apply, hx', hx] at h
    exact h

end Work.SymQuot.Chart
