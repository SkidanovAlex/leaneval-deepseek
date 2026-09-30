import Mathlib
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.AbVar.ProjectiveLine.isProper_P1
import Submission.Work.KeyLemma.Curve.p1_stalk_isDiscreteValuationRing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Extension of a morphism from a nonempty open of `ℙ¹`

Let `k` be a field, `V ⊆ ℙ¹_k` a nonempty open subscheme and `σ : V ⟶ A` a `k`-morphism into
a proper `k`-scheme `A`.  Then `σ` extends to a morphism `ℙ¹ ⟶ A`.

The proof runs the valuative criterion at the points of the complement of `V`.  Every point
`x ∉ V` has a *closed* specialisation `y` (the closed points of the Jacobson scheme `ℙ¹` are
dense in every closed subset, in particular in `closure {x} ⊆ ℙ¹ ∖ V`).  The local ring
`𝒪_{ℙ¹,y}` of `ℙ¹` at a closed point is a discrete valuation ring
(`Work.KeyLemma.Curve.p1_stalk_isDiscreteValuationRing`), so by the valuative criterion for
the proper `k`-scheme `A` the rational map `ℙ¹ ⇢ A` induced by `σ` is defined at `y`; the
locus of definition is open, so it contains `x` as well, since `x ⤳ y`.  A rational map which
is defined on all of `ℙ¹` is induced by a morphism, which is the required extension.
-/

open CategoryTheory AlgebraicGeometry Limits
universe u

namespace Work.KeyLemma.Curve

lemma fromSpecStalkOfMem_algebraMap {X : Scheme} [IrreducibleSpace X] (U : X.Opens) (x : X)
    (hx : x ∈ U) (hη : genericPoint X ∈ U) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      U.fromSpecStalkOfMem x hx = U.fromSpecStalkOfMem (genericPoint X) hη := by
  rw [← cancel_mono U.ι]
  rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [show (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))
      = X.presheaf.stalkSpecializes (genericPoint_specializes x) from by
        rw [CommRingCat.ofHom_hom]; rfl]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

lemma fromFunctionField_eq_specMap_fromSpecStalkOfMem {X Y : Scheme}
    [IrreducibleSpace X] (g : X.PartialMap Y) {x : X} (hx : x ∈ g.domain) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      g.fromSpecStalkOfMem hx = g.fromFunctionField := by
  rw [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc, fromSpecStalkOfMem_algebraMap]
  rfl

theorem mem_domain_of_valuationRing {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsProper (Y ↘ S)] [IsIntegral X] (f : X.PartialMap Y) [hf : f.IsOver S] {x : X}
    [ValuationRing (X.presheaf.stalk x)] [X.IsGermInjectiveAt x] :
    x ∈ f.toRationalMap.domain := by
  classical
  have hVC : ValuativeCriterion (Y ↘ S) := by
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType)
        (Y ↘ S) := by
      rw [← IsProper.eq_valuativeCriterion]
      exact inferInstance
    exact h.1.1.1
  have hf' : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) := by
    have := (Scheme.PartialMap.isOver_iff (S := S) (f := f)).mp hf
    simpa [Scheme.PartialMap.compHom_hom] using this
  have hcomm : f.fromFunctionField ≫ (Y ↘ S) =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (X.functionField))) ≫
        (X.fromSpecStalk x ≫ (X ↘ S)) := by
    rw [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, hf',
      ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [show (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (X.functionField)))
      = X.presheaf.stalkSpecializes (genericPoint_specializes x) from by
        rw [CommRingCat.ofHom_hom]; rfl]
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  let Sq : ValuativeCommSq (Y ↘ S) :=
    { R := ↥(X.presheaf.stalk x)
      domain := inferInstance
      K := ↥(X.functionField)
      i₁ := f.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ (X ↘ S)
      commSq := ⟨hcomm⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (ValuativeCriterion.existence hVC Sq).exists_lift.some
  let g : X.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk (x := x) (X ↘ S) (Y ↘ S) l hl₂
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hgl : g.fromSpecStalkOfMem hxg = l :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  have hgen : g.fromFunctionField = f.fromFunctionField := by
    rw [← fromFunctionField_eq_specMap_fromSpecStalkOfMem g hxg, hgl]
    exact hl₁
  have heq : g.toRationalMap = f.toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact hgen
  exact Scheme.RationalMap.mem_domain.mpr ⟨g, hxg, heq⟩

lemma topIso_inv_isoOfEq_hom_ι {X : Scheme} {U : X.Opens} (e : (⊤ : X.Opens) = U) :
    (Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ U.ι) = 𝟙 X := by
  rw [Scheme.isoOfEq_hom_ι, ← Scheme.topIso_hom, Iso.inv_hom_id]

lemma topIso_inv_isoOfEq_hom_comp {X : Scheme} {U : X.Opens} (e : (⊤ : X.Opens) = U)
    {W : Scheme} (f : X ⟶ W) :
    (Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ (U.ι ≫ f)) = f := by
  have h1 : (Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ (U.ι ≫ f))
      = ((Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ U.ι)) ≫ f := by
    simp only [Category.assoc]
  rw [h1, topIso_inv_isoOfEq_hom_ι, Category.id_comp]

lemma ι_comp_topIso_inv_isoOfEq_hom {X : Scheme} {U : X.Opens} (e : (⊤ : X.Opens) = U)
    {V : X.Opens} (h : V ≤ U) :
    V.ι ≫ ((Scheme.topIso X).inv ≫ (X.isoOfEq e).hom) = X.homOfLE h := by
  rw [← cancel_mono U.ι]
  have h1 : (V.ι ≫ ((Scheme.topIso X).inv ≫ (X.isoOfEq e).hom)) ≫ U.ι
      = V.ι ≫ ((Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ U.ι)) := by
    simp only [Category.assoc]
  rw [h1, Scheme.isoOfEq_hom_ι, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id,
    Scheme.homOfLE_ι]

lemma ι_comp_topIso_inv_isoOfEq_hom_comp {X : Scheme} {U : X.Opens} (e : (⊤ : X.Opens) = U)
    {V : X.Opens} (h : V ≤ U) {W : Scheme} (f : ↑U ⟶ W) :
    V.ι ≫ ((Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ f)) = X.homOfLE h ≫ f := by
  have h1 : V.ι ≫ ((Scheme.topIso X).inv ≫ ((X.isoOfEq e).hom ≫ f))
      = (V.ι ≫ ((Scheme.topIso X).inv ≫ (X.isoOfEq e).hom)) ≫ f := by
    simp only [Category.assoc]
  rw [h1, ι_comp_topIso_inv_isoOfEq_hom e h]

theorem extends_of_open_p1 {k : Type u} [Field k]
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [AlgebraicGeometry.IsProper A.hom]
    (V : (Work.AbVar.P1 k).left.Opens) (hV : (V : Set (Work.AbVar.P1 k).left).Nonempty)
    (σ : V.toScheme ⟶ A.left)
    (hσ : CategoryTheory.CategoryStruct.comp σ A.hom =
      CategoryTheory.CategoryStruct.comp V.ι (Work.AbVar.P1 k).hom) :
    ∃ σbar : (Work.AbVar.P1 k).left ⟶ A.left,
      CategoryTheory.CategoryStruct.comp σbar A.hom = (Work.AbVar.P1 k).hom ∧
      CategoryTheory.CategoryStruct.comp V.ι σbar = σ := by
  classical
  haveI hInt : IsIntegral ((Work.AbVar.P1 k).left) := Work.AbVar.ProjectiveLine.isIntegral_P1 k
  haveI hProperP1 : IsProper ((Work.AbVar.P1 k).hom) := Work.AbVar.ProjectiveLine.isProper_P1 k
  haveI hJacob : JacobsonSpace ((Work.AbVar.P1 k).left) :=
    LocallyOfFiniteType.jacobsonSpace (Work.AbVar.P1 k).hom
  let S := Spec (CommRingCat.of k)
  haveI hProperA : IsProper (A.left ↘ S) := by
    have h : IsProper A.hom := inferInstance
    exact h
  have hVdense : Dense (V : Set (Work.AbVar.P1 k).left) := V.2.dense hV
  let f : (Work.AbVar.P1 k).left.PartialMap A.left :=
    { domain := V, dense_domain := hVdense, hom := σ }
  haveI hfOver : f.IsOver S := ⟨by
    show f.hom ≫ (A.left ↘ S) = (↑f.domain ↘ S)
    rw [show (A.left ↘ S) = A.hom from rfl]
    exact hσ⟩
  have hdom : ∀ x : (Work.AbVar.P1 k).left, x ∈ f.toRationalMap.domain := by
    intro x
    by_cases hx : x ∈ V
    · exact f.le_domain_toRationalMap hx
    · obtain ⟨y, hyZ, hycl⟩ := nonempty_inter_closedPoints
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
  have hd' : (⊤ : (Work.AbVar.P1 k).left.Opens) = (f.toRationalMap.toPartialMap).domain := hd.symm
  have hgo : (f.toRationalMap.toPartialMap).hom ≫ A.hom
      = (f.toRationalMap.toPartialMap).domain.ι ≫ (Work.AbVar.P1 k).hom := by
    have h : (f.toRationalMap.toPartialMap).hom ≫ (A.left ↘ S)
        = (↑(f.toRationalMap.toPartialMap).domain ↘ S) :=
      (inferInstance : HomIsOver (f.toRationalMap.toPartialMap).hom S).comp_over
    rwa [show (A.left ↘ S) = A.hom from rfl,
      show (↑(f.toRationalMap.toPartialMap).domain ↘ S)
        = (f.toRationalMap.toPartialMap).domain.ι ≫ ((Work.AbVar.P1 k).left ↘ S) from rfl,
      show ((Work.AbVar.P1 k).left ↘ S) = (Work.AbVar.P1 k).hom from rfl] at h
  let σbar : (Work.AbVar.P1 k).left ⟶ A.left :=
    (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hd').hom ≫ (f.toRationalMap.toPartialMap).hom
  have hσbar : σbar = (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hd').hom
      ≫ (f.toRationalMap.toPartialMap).hom := rfl
  refine ⟨σbar, ?_, ?_⟩
  · rw [hσbar]
    simp only [Category.assoc]
    rw [hgo]
    exact topIso_inv_isoOfEq_hom_comp hd' (Work.AbVar.P1 k).hom
  · have hres := Scheme.PartialMap.toPartialMap_toRationalMap_restrict f
    have hgoal : V.ι ≫ σbar = f.hom := by
      rw [hσbar, ← hres]
      rw [show (f.toRationalMap.toPartialMap.restrict f.domain f.dense_domain
            f.le_domain_toRationalMap).hom
          = ((Work.AbVar.P1 k).left).homOfLE f.le_domain_toRationalMap
              ≫ (f.toRationalMap.toPartialMap).hom from rfl]
      exact ι_comp_topIso_inv_isoOfEq_hom_comp hd' f.le_domain_toRationalMap
        (f.toRationalMap.toPartialMap).hom
    exact hgoal

end Work.KeyLemma.Curve
