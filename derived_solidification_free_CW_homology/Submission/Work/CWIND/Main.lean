/-
Copyright (c) 2026 The CWIND team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.AFun.exists_aNat
import Submission.Work.CWIND.AFun.aNat_solidEquiv
import Submission.Work.CWIND.BFun.exists_bNat
import Submission.Work.CWIND.BFun.bLevel_isIso_of_subsingleton
import Submission.Work.CWIND.Homotopy.dFree_homotopy
import Submission.Work.CWIND.Homotopy.dFree_constMap
import Submission.Work.CWIND.GClass.G_sigma
import Submission.Work.CWIND.GClass.G_mv
import Submission.Work.CWIND.GClass.G_exhaust
import Submission.Work.CWIND.GClass.G_homotopyEquiv
import Submission.Work.CWIND.GClass.G_point_empty
import Submission.Work.CWIND.Cofibrant.C_solidCofibrant
import Submission.Work.CWIND.Cofibrant.iso_solDerivedInclusion

/-!
# CWIND — the natural comparison with singular chains (hole 10)

Main definitions and results:

* `Work.CWIND.aNat` — the natural comparison map `ℤ[X][0] ⟶ A(X)` (inclusion in degree `0`);
* `Work.CWIND.bNat` — the natural comparison map `C_sing(X) ⟶ A(X)` induced levelwise by the
  identity from the discrete topology (`Work.CWIND.bLevel`);
* `Work.CWIND.aNat_solidEquiv` — `a(X)` is a solid-equivalence for Hausdorff `X`;
* `Work.CWIND.cwClosed_GOf` and `Work.CWIND.bNat_solidEquiv_of_CW` — `b(X)` is a solid-equivalence
  for every Hausdorff CW complex `X` (CW induction through the closure class `GOf bNat`);
* `Work.CWIND.cwIso_prop : Submission.Blueprint.CWIsoProp` — the natural isomorphism
  `ι_D (L (Q (ℤ[X][0]))) ≅ Q C_sing(X)` of hole 10.
-/

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed
open scoped Simplicial
open Opposite

namespace Work.CWIND

open _root_.LightCondensed _root_.LightCondensed.Solid Submission.Blueprint

/-- The degree-`0` comparison map `a : ℤ[X][0] ⟶ A(X)`, as a natural transformation of cochain
complexes (its degree-`0` component is `a0`). -/
noncomputable def aNat :
    freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor :=
  Classical.choose AFun.exists_aNat

lemma aNat_f_zero (X : TopCat.{0}) :
    (aNat.app X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (freeLightCondAbOfTop X)).hom ≫
        a0 X :=
  (Classical.choose_spec AFun.exists_aNat) X

/-- The comparison map `b : C_sing(X) ⟶ A(X)`, induced levelwise by the identity from the discrete
topology on the set of singular simplices. -/
noncomputable def bNat : singularChainsLightCondAbComplexFunctor ⟶ AFunctor :=
  Classical.choose BFun.exists_bNat

lemma bNat_f (X : TopCat.{0}) (n : ℕ) :
    (bNat.app X).f (-(n : ℤ)) = (CXIso X n).inv ≫ bLevel X n ≫ (AXIso X n).inv :=
  (Classical.choose_spec BFun.exists_bNat) X n

lemma bLevel_isIso_of_subsingleton' (X : TopCat.{0}) [Subsingleton ↥X] (n : ℕ) :
    IsIso (bLevel X n) :=
  BFun.bLevel_isIso_of_subsingleton X n

/-- **`a` is a solid-equivalence for Hausdorff spaces** (REFS/05 §1). -/
theorem aNat_solidEquiv (hD : DerivedProp) (hTK : ToolkitProp) (hHI : HIProp)
    [isSolid.ι.IsRightAdjoint] (D : DerivedPackage) (X : TopCat.{0}) [T2Space X] :
    SolidEquiv ((DerivedCategory.Q).map (aNat.app X)) :=
  AFun.aNat_solidEquiv hD D hHI hTK aNat aNat_f_zero
    (fun Y _ n => Homotopy.dFree_constMap Y n (Homotopy.dFree_homotopy hD D hHI hTK).2) X

/-- **The class `GOf bNat` satisfies the closure axioms of `CWClosed`** (REFS/05 §2). -/
theorem cwClosed_GOf (hD : DerivedProp) (hTK : ToolkitProp) (hHI : HIProp)
    (hCondMV : CondMVProp) (hSingMV : SingMVProp) [isSolid.ι.IsRightAdjoint]
    (D : DerivedPackage) : CWClosed (GOf bNat) := by
  have hA2 : ∀ {Y Z : TopCat.{0}} [T2Space Y] [T2Space Z]
      (e : ContinuousMap.HomotopyEquiv ↥Y ↥Z), SolidEquiv (dFree (TopCat.ofHom e.toFun)) :=
    (Homotopy.dFree_homotopy hD D hHI hTK).2
  have hconst : ∀ (X : TopCat.{0}) [T2Space X] (n : ℕ),
      SolidEquiv (dFree (constMap X n)) :=
    fun X _ n => Homotopy.dFree_constMap X n hA2
  have hA : ∀ (Y : TopCat.{0}) [T2Space Y],
      SolidEquiv ((DerivedCategory.Q).map (aNat.app Y)) :=
    fun Y _ => AFun.aNat_solidEquiv hD D hHI hTK aNat aNat_f_zero hconst Y
  have hpt := GClass.G_point_empty bNat bNat_f bLevel_isIso_of_subsingleton'
  exact
    { point := hpt.1
      empty := hpt.2
      of_homotopyEquiv := fun X Y _ _ e hY => GClass.G_homotopyEquiv hTK aNat hA hA2 bNat e hY
      sigma := fun J X _ h => GClass.G_sigma hTK bNat J X h
      mv := fun X _ U V hU hV hUV hU' hV' hUV' =>
        GClass.G_mv hTK hCondMV hSingMV aNat hA bNat X U V hU hV hUV hU' hV' hUV'
      exhaust := fun X _ A hmono hcpt hG => GClass.G_exhaust hTK bNat X A hmono hcpt hG }

/-- **`b` is a solid-equivalence for Hausdorff CW complexes** (REFS/05 §2–3). -/
theorem bNat_solidEquiv_of_CW (hD : DerivedProp) (hTK : ToolkitProp) (hHI : HIProp)
    (hCondMV : CondMVProp) (hSingMV : SingMVProp) (hCwTop : CWTopProp)
    [isSolid.ι.IsRightAdjoint] (D : DerivedPackage) (X : TopCat.{0}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    SolidEquiv ((DerivedCategory.Q).map (bNat.app X)) :=
  (hCwTop (GOf bNat) (cwClosed_GOf hD hTK hHI hCondMV hSingMV D) X).2

/-- **Area CWIND (hole 10).** For every derived package `D`, the derived inclusion of the derived
solidification of the free light condensed abelian group on a CW complex `X` is naturally
isomorphic to the integral singular chain complex of `X` (with homological degree `n` placed in
cohomological degree `-n`), as a functor on `CWTopCat`. -/
theorem cwIso_prop (hD : DerivedProp) (hRes : ResolutionProp) (hTK : ToolkitProp)
    (hHI : HIProp) (hDisc : DiscProp) (hCondMV : CondMVProp) (hSingMV : SingMVProp)
    (hCwTop : CWTopProp) : CWIsoProp := by
  intro inst D
  -- `a` is a solid-equivalence at Hausdorff spaces and `b` at Hausdorff CW complexes.
  have hA : ∀ (Y : TopCat.{0}) [T2Space Y],
      SolidEquiv ((DerivedCategory.Q).map (aNat.app Y)) :=
    fun Y _ => aNat_solidEquiv hD hTK hHI D Y
  have hsolid : ∀ (X : TopCat.{0}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)],
      SolidEquiv ((DerivedCategory.Q).map (bNat.app X)) :=
    fun X _ _ => bNat_solidEquiv_of_CW hD hTK hHI hCondMV hSingMV hCwTop D X
  -- The singular chain complex is solid-cofibrant, and derived solidification changes nothing.
  have hcof : ∀ X : TopCat.{0},
      SolidCofibrant (singularChainsLightCondAbComplexFunctor.obj X) :=
    fun X => Cofibrant.C_solidCofibrant hDisc hRes X
  obtain ⟨eC⟩ := Cofibrant.iso_solDerivedInclusion hD D hDisc hcof
  -- The three pieces of the natural zigzag.
  have isoA : (CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙
        (CochainComplex.singleFunctor LightCondAb 0 ⋙ (DerivedCategory.Q ⋙
          (D.L ⋙ derivedInclusion)))) ≅
      (CWTopCat.toTopCat ⋙ AFunctor ⋙ (DerivedCategory.Q ⋙ (D.L ⋙ derivedInclusion))) :=
    NatIso.ofComponents
      (fun X => by
        haveI : T2Space ↥X.obj := X.property.1
        haveI h1 : IsIso ((D.L).map (DerivedCategory.Q.map (aNat.app X.obj))) :=
          (hD.2 D (DerivedCategory.Q.map (aNat.app X.obj))).mp (hA X.obj)
        haveI : IsIso (derivedInclusion.map
            ((D.L).map (DerivedCategory.Q.map (aNat.app X.obj)))) :=
          Functor.map_isIso derivedInclusion _
        exact asIso (derivedInclusion.map ((D.L).map (DerivedCategory.Q.map (aNat.app X.obj)))))
      (naturality := fun {X Y} f => by
        have h := (Functor.whiskerLeft CWTopCat.toTopCat
          (Functor.whiskerRight aNat (DerivedCategory.Q ⋙ D.L ⋙ derivedInclusion))).naturality f
        simp only [Functor.assoc, Functor.comp_map] at h ⊢
        exact h)
  have isoB : (CWTopCat.toTopCat ⋙ singularChainsLightCondAbComplexFunctor ⋙
        (DerivedCategory.Q ⋙ (D.L ⋙ derivedInclusion))) ≅
      (CWTopCat.toTopCat ⋙ AFunctor ⋙ (DerivedCategory.Q ⋙ (D.L ⋙ derivedInclusion))) :=
    NatIso.ofComponents
      (fun X => by
        haveI : T2Space ↥X.obj := X.property.1
        haveI : Topology.CWComplex (Set.univ : Set ↥X.obj) := Classical.choice X.property.2
        haveI h2 : IsIso ((D.L).map (DerivedCategory.Q.map (bNat.app X.obj))) :=
          (hD.2 D (DerivedCategory.Q.map (bNat.app X.obj))).mp (hsolid X.obj)
        haveI : IsIso (derivedInclusion.map
            ((D.L).map (DerivedCategory.Q.map (bNat.app X.obj)))) :=
          Functor.map_isIso derivedInclusion _
        exact asIso (derivedInclusion.map ((D.L).map (DerivedCategory.Q.map (bNat.app X.obj)))))
      (naturality := fun {X Y} f => by
        have h := (Functor.whiskerLeft CWTopCat.toTopCat
          (Functor.whiskerRight bNat (DerivedCategory.Q ⋙ D.L ⋙ derivedInclusion))).naturality f
        simp only [Functor.assoc, Functor.comp_map] at h ⊢
        exact h)
  have eC' : (CWTopCat.toTopCat ⋙ singularChainsLightCondAbComplexFunctor ⋙
        (DerivedCategory.Q ⋙ (D.L ⋙ derivedInclusion))) ≅
      (CWTopCat.toTopCat ⋙ singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q) :=
    NatIso.ofComponents (fun X => eC.app X.obj)
      (naturality := fun {X Y} f => by
        have h := eC.hom.naturality (CWTopCat.toTopCat.map f)
        simp only [Functor.assoc, Functor.comp_map] at h ⊢
        exact h)
  have isoAll := isoA.trans (isoB.symm.trans eC')
  exact ⟨NatIso.ofComponents (fun X => isoAll.app X)
    (naturality := fun {X Y} f => isoAll.hom.naturality f)⟩

end Work.CWIND
