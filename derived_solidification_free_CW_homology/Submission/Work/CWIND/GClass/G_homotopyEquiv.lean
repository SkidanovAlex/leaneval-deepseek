import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-!
# CWIND/T10 — the homotopy-equivalence field of the CW induction

This file proves `Work.CWIND.GClass.G_homotopyEquiv`, the field `of_homotopyEquiv` of the class
`CWClosed` for the class `GOf b` of spaces whose singular chains compute `A` up to
solid-equivalence.

The mathematical content is entirely formal:

* the singular chain map of a homotopy equivalence of spaces is a homotopy equivalence of chain
  complexes (Mathlib's homotopy invariance of singular chains, pushed through the discrete and
  `extend` functors), hence an isomorphism in the derived category, hence a solid-equivalence
  (`ToolkitProp.of_iso`);
* naturality of the comparison maps `a : ℤ[-] ⟶ A` and `b : C_sing(-) ⟶ A` gives two commuting
  squares in the derived category, and the two-out-of-three properties of `ToolkitProp` finish.

The only library gap filled here is the additivity of the discrete functor
`LightCondensed.discrete (ModuleCat ℤ)`, which Mathlib knows for `constantSheaf` but not for its
(unfolding) definition `LightCondensed.discrete`; it is installed locally as a `haveI` in the
auxiliary lemma below.
-/

/-- The singular chain complex functor sends homotopic maps of spaces to homotopic chain maps.

This is the composite of Mathlib's `TopCat.Homotopy.singularChainComplexFunctorObjMap` with the
two functors `(LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)`
and `ComplexShape.embeddingDownNat.extendFunctor LightCondAb` making up
`singularChainsLightCondAbComplexFunctor`; homotopies are pushed through additive functors by
`CategoryTheory.Functor.mapHomotopy`, and through the shape embedding by `Homotopy.extend`. -/
noncomputable def homotopy_singularChains {A B : TopCat.{0}} {u v : A ⟶ B} (h : TopCat.Homotopy u v) :
    Homotopy (singularChainsLightCondAbComplexFunctor.map u)
      (singularChainsLightCondAbComplexFunctor.map v) := by
  haveI : (LightCondensed.discrete (ModuleCat.{0} ℤ)).Additive :=
    inferInstanceAs ((CategoryTheory.constantSheaf (CategoryTheory.coherentTopology LightProfinite)
      (ModuleCat.{0} ℤ)).Additive)
  have hS : Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map u)
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map v) :=
    TopCat.Homotopy.singularChainComplexFunctorObjMap h (ModuleCat.of ℤ ℤ)
  have hD : Homotopy
      (((LightCondensed.discrete (ModuleCat.{0} ℤ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map u))
      (((LightCondensed.discrete (ModuleCat.{0} ℤ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map v)) :=
    CategoryTheory.Functor.mapHomotopy (LightCondensed.discrete (ModuleCat.{0} ℤ)) hS
  exact hD.extend ComplexShape.embeddingDownNat

/-- **CWIND/T10 (the homotopy-equivalence field of the CW induction).**  If `f : X ≃ₕ Y` is a
homotopy equivalence of Hausdorff spaces and `Y` lies in `GOf b`, then so does `X` — REFS/05
section 2.  Naturality of `b` gives the square relating `b(X)`, `b(Y)`, the singular chains of `f`
and `A(f)`.  The singular chain map of `f` is a quasi-isomorphism (Mathlib's homotopy invariance of
singular chains), hence a solid-equivalence via `ToolkitProp.of_iso`; `A(f)` is a solid-equivalence
because naturality of `a` identifies `single 0 (ℤ[f]) = dFree f` with `A(f)` up to the
solid-equivalences `a(X)`, `a(Y)`, and `dFree f` is a solid-equivalence by `hA2`.  Two-out-of-three
for `b` then gives the claim. -/
theorem G_homotopyEquiv (hTK : ToolkitProp)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor)
    (hA : ∀ (Y : TopCat.{0}) [T2Space Y], SolidEquiv ((DerivedCategory.Q).map (a.app Y)))
    (hA2 : ∀ {Y Z : TopCat.{0}} [T2Space Y] [T2Space Z] (e : ContinuousMap.HomotopyEquiv ↥Y ↥Z),
      SolidEquiv (dFree (TopCat.ofHom e.toFun)))
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    {X Y : TopCat.{0}} [T2Space X] [T2Space Y] (e : ContinuousMap.HomotopyEquiv ↥X ↥Y)
    (hY : GOf b Y) : GOf b X := by
  refine ⟨inferInstance, ?_⟩
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  -- The singular chain map of the homotopy equivalence `f` is a solid-equivalence, because it is
  -- a homotopy equivalence of complexes, hence an isomorphism in the derived category.
  have hcf : SolidEquiv
      ((DerivedCategory.Q).map (singularChainsLightCondAbComplexFunctor.map f)) := by
    have hcc1 : Homotopy
        (singularChainsLightCondAbComplexFunctor.map f ≫
          singularChainsLightCondAbComplexFunctor.map g)
        (𝟙 (singularChainsLightCondAbComplexFunctor.obj X)) := by
      have hh := homotopy_singularChains h1
      rw [singularChainsLightCondAbComplexFunctor.map_comp,
        singularChainsLightCondAbComplexFunctor.map_id] at hh
      exact hh
    have hcc2 : Homotopy
        (singularChainsLightCondAbComplexFunctor.map g ≫
          singularChainsLightCondAbComplexFunctor.map f)
        (𝟙 (singularChainsLightCondAbComplexFunctor.obj Y)) := by
      have hh := homotopy_singularChains h2
      rw [singularChainsLightCondAbComplexFunctor.map_comp,
        singularChainsLightCondAbComplexFunctor.map_id] at hh
      exact hh
    haveI : QuasiIso (singularChainsLightCondAbComplexFunctor.map f) :=
      HomotopyEquiv.quasiIso_hom
        { hom := singularChainsLightCondAbComplexFunctor.map f
          inv := singularChainsLightCondAbComplexFunctor.map g
          homotopyHomInvId := hcc1
          homotopyInvHomId := hcc2 }
    exact hTK.of_iso _ inferInstance
  -- Naturality of `a` in the derived category.
  have haNat : dFree f ≫ (DerivedCategory.Q).map (a.app Y) =
      (DerivedCategory.Q).map (a.app X) ≫ (DerivedCategory.Q).map (AFunctor.map f) := by
    have h := congrArg (fun (m : (freeLightCondAbOfTopFunctor ⋙
        (CochainComplex.singleFunctor LightCondAb 0)).obj X ⟶ AFunctor.obj Y) =>
        (DerivedCategory.Q).map m) (a.naturality f)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  -- Hence `A(f)` is a solid-equivalence.
  have hAFf : SolidEquiv ((DerivedCategory.Q).map (AFunctor.map f)) := by
    have hc := hTK.comp (dFree f) ((DerivedCategory.Q).map (a.app Y)) (hA2 e) (hA Y)
    rw [haNat] at hc
    exact hTK.of_comp_left ((DerivedCategory.Q).map (a.app X))
      ((DerivedCategory.Q).map (AFunctor.map f)) (hA X) hc
  -- Naturality of `b` in the derived category.
  have hbNat : (DerivedCategory.Q).map (singularChainsLightCondAbComplexFunctor.map f) ≫
      (DerivedCategory.Q).map (b.app Y) =
        (DerivedCategory.Q).map (b.app X) ≫ (DerivedCategory.Q).map (AFunctor.map f) := by
    have h := congrArg (fun (m : singularChainsLightCondAbComplexFunctor.obj X ⟶ AFunctor.obj Y) =>
      (DerivedCategory.Q).map m) (b.naturality f)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  -- Two-out-of-three.
  have hc := hTK.comp ((DerivedCategory.Q).map (singularChainsLightCondAbComplexFunctor.map f))
    ((DerivedCategory.Q).map (b.app Y)) hcf hY.2
  rw [hbNat] at hc
  exact hTK.of_comp_right ((DerivedCategory.Q).map (b.app X))
    ((DerivedCategory.Q).map (AFunctor.map f)) hAFf hc

end Work.CWIND.GClass
