import Mathlib
import Submission.Work.KeyLemma.Curve.extends_of_open_p1
import Submission.Work.KeyLemma.Curve.p1_stalk_isDiscreteValuationRing
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.AbVar.ProjectiveLine.isProper_P1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.KeyLemma.Curve

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

universe u

/-! ## Auxiliary lemmas about `fromSpecStalkOfMem` and the top-open iso. -/

/-- `fromSpecStalkOfMem` does not depend on the proof of membership in the domain. -/
lemma fromSpecStalkOfMem_congr {X Y : Scheme} (F : X.PartialMap Y) {x : X}
    (hx hx' : x ∈ F.domain) :
    F.fromSpecStalkOfMem hx = F.fromSpecStalkOfMem hx' := by
  simp only [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.Opens.fromSpecStalkOfMem]

/-- Precomposing a morphism built from a partial map whose domain is all of `X`
with `X.fromSpecStalk x` recovers `fromSpecStalkOfMem`. -/
lemma fromSpecStalk_comp_topIso_inv_isoOfEq {X Y : Scheme} (F : X.PartialMap Y)
    (hd' : (⊤ : X.Opens) = F.domain) (x : X) (hx : x ∈ F.domain) :
    X.fromSpecStalk x ≫ ((Scheme.topIso X).inv ≫ (Scheme.isoOfEq X hd').hom ≫ F.hom)
      = F.fromSpecStalkOfMem hx := by
  rw [Scheme.PartialMap.fromSpecStalkOfMem]
  rw [← show X.fromSpecStalk x ≫ ((Scheme.topIso X).inv ≫ (Scheme.isoOfEq X hd').hom)
      = F.domain.fromSpecStalkOfMem x hx from by
    rw [← cancel_mono F.domain.ι]
    simp only [Category.assoc]
    rw [Scheme.isoOfEq_hom_ι]
    rw [← Scheme.topIso_hom]
    rw [Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [Iso.inv_hom_id, Category.comp_id]]
  simp only [Category.assoc]

/--
Let `k` be a field and `A` a proper `k`-scheme.  Every `k`-morphism
`Spec K(ℙ¹) ⟶ A` from the generic point of `ℙ¹` extends to a `k`-morphism
`ℙ¹ ⟶ A` inducing it on the generic point.
-/
theorem extends_of_stalk_genericPoint_p1 {k : Type u} [Field k]
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [AlgebraicGeometry.IsProper A.hom]
    [AlgebraicGeometry.IsIntegral (Work.AbVar.P1 k).left]
    (g : AlgebraicGeometry.Spec (CommRingCat.of ↥(Work.AbVar.P1 k).left.functionField) ⟶ A.left)
    (hg : g ≫ A.hom = (Work.AbVar.P1 k).left.fromSpecStalk
        (genericPoint (Work.AbVar.P1 k).left) ≫ (Work.AbVar.P1 k).hom) :
    ∃ σ : (Work.AbVar.P1 k).left ⟶ A.left,
      σ ≫ A.hom = (Work.AbVar.P1 k).hom ∧
      (Work.AbVar.P1 k).left.fromSpecStalk
          (genericPoint (Work.AbVar.P1 k).left) ≫ σ = g := by
  classical
  haveI hProperP1 : IsProper ((Work.AbVar.P1 k).hom) := Work.AbVar.ProjectiveLine.isProper_P1 k
  haveI hJacob : JacobsonSpace ((Work.AbVar.P1 k).left) :=
    LocallyOfFiniteType.jacobsonSpace (Work.AbVar.P1 k).hom
  let S := Spec (CommRingCat.of k)
  haveI hProperA : IsProper (A.left ↘ S) := by
    have h : IsProper A.hom := inferInstance
    exact h
  let f : (Work.AbVar.P1 k).left.PartialMap A.left :=
    Scheme.PartialMap.ofFromSpecStalk (Work.AbVar.P1 k).hom A.hom g hg
  haveI hfOver : f.IsOver S :=
    ⟨Scheme.PartialMap.ofFromSpecStalk_comp (Work.AbVar.P1 k).hom A.hom g hg⟩
  have hdom : ∀ x : (Work.AbVar.P1 k).left, x ∈ f.toRationalMap.domain := by
    intro x
    obtain ⟨y, hyZ, hycl⟩ := nonempty_inter_closedPoints
        (Z := closure ({x} : Set (Work.AbVar.P1 k).left)) ⟨x, subset_closure rfl⟩
        isClosed_closure.isLocallyClosed
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hyZ
    haveI hDVR : IsDiscreteValuationRing ((Work.AbVar.P1 k).left.presheaf.stalk y) :=
      p1_stalk_isDiscreteValuationRing (k := k) y hycl
    haveI hVR : ValuationRing ((Work.AbVar.P1 k).left.presheaf.stalk y) := inferInstance
    have hy : y ∈ f.toRationalMap.domain := mem_domain_of_valuationRing (S := S) f
    exact hxy.mem_open f.toRationalMap.domain.2 hy
  have hd : f.toRationalMap.domain = ⊤ := le_antisymm le_top (fun x _ => hdom x)
  haveI hRed : IsReduced ((Work.AbVar.P1 k).left) := inferInstance
  haveI hSepA : A.left.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from A.hom]
    infer_instance⟩
  have hd' : (⊤ : (Work.AbVar.P1 k).left.Opens) = (f.toRationalMap.toPartialMap).domain :=
    hd.symm
  let σbar : (Work.AbVar.P1 k).left ⟶ A.left :=
    (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hd').hom ≫ (f.toRationalMap.toPartialMap).hom
  have hσbar : σbar = (Scheme.topIso (Work.AbVar.P1 k).left).inv
      ≫ (Scheme.isoOfEq (Work.AbVar.P1 k).left hd').hom
      ≫ (f.toRationalMap.toPartialMap).hom := rfl
  refine ⟨σbar, ?_, ?_⟩
  · have hgo : (f.toRationalMap.toPartialMap).hom ≫ A.hom
        = (f.toRationalMap.toPartialMap).domain.ι ≫ (Work.AbVar.P1 k).hom := by
      have h : (f.toRationalMap.toPartialMap).hom ≫ (A.left ↘ S)
          = (↑(f.toRationalMap.toPartialMap).domain ↘ S) :=
        (inferInstance : HomIsOver (f.toRationalMap.toPartialMap).hom S).comp_over
      rwa [show (A.left ↘ S) = A.hom from rfl,
        show (↑(f.toRationalMap.toPartialMap).domain ↘ S)
          = (f.toRationalMap.toPartialMap).domain.ι ≫ ((Work.AbVar.P1 k).left ↘ S) from rfl,
        show ((Work.AbVar.P1 k).left ↘ S) = (Work.AbVar.P1 k).hom from rfl] at h
    rw [hσbar]
    simp only [Category.assoc]
    rw [hgo]
    exact topIso_inv_isoOfEq_hom_comp hd' (Work.AbVar.P1 k).hom
  · have hFff : (f.toRationalMap.toPartialMap).fromFunctionField = g := by
      rw [← Scheme.RationalMap.fromFunctionField_toRationalMap (f.toRationalMap.toPartialMap),
        Scheme.RationalMap.toRationalMap_toPartialMap]
      exact Scheme.RationalMap.fromFunctionField_ofFunctionField (Work.AbVar.P1 k).hom A.hom g hg
    have hx : genericPoint (Work.AbVar.P1 k).left ∈ (f.toRationalMap.toPartialMap).domain := by
      rw [← hd']; exact trivial
    have hkey : (Work.AbVar.P1 k).left.fromSpecStalk (genericPoint (Work.AbVar.P1 k).left) ≫ σbar
        = (f.toRationalMap.toPartialMap).fromSpecStalkOfMem hx := by
      rw [hσbar]
      exact fromSpecStalk_comp_topIso_inv_isoOfEq _ hd' _ hx
    rw [hkey, show (f.toRationalMap.toPartialMap).fromSpecStalkOfMem hx
        = (f.toRationalMap.toPartialMap).fromFunctionField from
      (fromSpecStalkOfMem_congr _ hx _).trans rfl]
    exact hFff

end Work.KeyLemma.Curve
