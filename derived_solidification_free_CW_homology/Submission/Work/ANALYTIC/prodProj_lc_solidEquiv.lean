import Mathlib
import Submission.Work.ANALYTIC.HICond
import Submission.Work.ANALYTIC.profinite_HI

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

attribute [local instance] lightCondSetHasCoproduct

/-!
## AN5 transported along the canonical isomorphism `lc S ≅ T S`

The two comparison steps of `Work.ANALYTIC.prodProj_lc_solidEquiv`:

* `muIso_hom_comp_map_prTop` identifies the topological projection `prTop Y` with the condensed
  first projection `prodProj (T Y)` under the tensorator of `topCatToLightCondSet`;
* `solidEquiv_of_iso_left` / `solidEquiv_of_iso_right` / `solidEquiv_comp_iso` record that
  `SolidEquiv` is invariant under pre- and post-composition with isomorphisms.
-/

/-- The tensorator of `topCatToLightCondSet` carries the topological projection `prTop Y` to the
condensed projection `prodProj (T Y)`. -/
lemma muIso_hom_comp_map_prTop (Y : TopCat.{0}) :
    (Functor.Monoidal.μIso topCatToLightCondSet Y unitIntervalTopCat).hom ≫
      topCatToLightCondSet.map (prTop Y) = prodProj (topCatToLightCondSet.obj Y) := by
  rw [prTop_eq_fst, Functor.Monoidal.μIso_hom]
  exact (@Functor.Monoidal.μ_fst TopCat _ _ LightCondSet _ _ topCatToLightCondSet
    instMonoidalTopCatToLightCondSet Y unitIntervalTopCat).trans
      (SemiCartesianMonoidalCategory.fst_def _ _)

/-- `prodProj` is natural: it is the first projection of the product with the interval. -/
lemma prodProj_nat {X Y : LightCondSet.{0}} (f : X ⟶ Y) :
    (f ▷ Icond) ≫ prodProj Y = prodProj X ≫ f := by
  rw [prodProj, prodProj, ← Category.assoc,
    ← MonoidalCategory.whisker_exchange f (SemiCartesianMonoidalCategory.toUnit Icond),
    Category.assoc]
  erw [MonoidalCategory.rightUnitor_naturality]
  rw [Category.assoc]

/-- Precomposition with an isomorphism is a bijection on morphisms into a fixed target. -/
lemma bijective_precomp_iso_hom {X Y Z : DLightCondAb} (e : X ≅ Y) :
    Function.Bijective (fun k : Y ⟶ Z => e.hom ≫ k) := by
  refine ⟨fun a b h => ?_, fun b => ⟨e.inv ≫ b, ?_⟩⟩
  · have h' : e.hom ≫ a = e.hom ≫ b := h
    calc a = e.inv ≫ (e.hom ≫ a) := (Iso.inv_hom_id_assoc e a).symm
      _ = e.inv ≫ (e.hom ≫ b) := by rw [h']
      _ = b := Iso.inv_hom_id_assoc e b
  · exact Iso.hom_inv_id_assoc e b

/-- Postcomposition with the inverse of an isomorphism is a bijection on morphisms out of a fixed
source. -/
lemma bijective_precomp_iso_inv {X Y Z : DLightCondAb} (e : X ≅ Y) :
    Function.Bijective (fun k : X ⟶ Z => e.inv ≫ k) := by
  simpa only [Iso.symm_hom] using bijective_precomp_iso_hom e.symm

/-- `SolidEquiv` is invariant under precomposition with an isomorphism. -/
lemma solidEquiv_of_iso_left {A B C : DLightCondAb} (u : A ≅ B) (F : B ⟶ C) :
    Submission.Blueprint.SolidEquiv (u.hom ≫ F) ↔ Submission.Blueprint.SolidEquiv F := by
  have hfun : ∀ N : DSolid,
      (fun k : C ⟶ derivedInclusion.obj N => (u.hom ≫ F) ≫ k) =
        (fun m : B ⟶ derivedInclusion.obj N => u.hom ≫ m) ∘
          (fun k : C ⟶ derivedInclusion.obj N => F ≫ k) := by
    intro N
    funext k
    simp only [Function.comp_apply, Category.assoc]
  constructor
  · intro h
    intro N
    have hb : Function.Bijective
        (fun k : C ⟶ derivedInclusion.obj N => (u.hom ≫ F) ≫ k) :=
      (show ∀ N : DSolid, Function.Bijective
        (fun k : C ⟶ derivedInclusion.obj N => (u.hom ≫ F) ≫ k) from h) N
    rw [hfun N] at hb
    exact (Function.Bijective.of_comp_iff' (bijective_precomp_iso_hom u)
      (fun k : C ⟶ derivedInclusion.obj N => F ≫ k)).mp hb
  · intro h
    intro N
    have hb : Function.Bijective (fun k : C ⟶ derivedInclusion.obj N => F ≫ k) :=
      (show ∀ N : DSolid, Function.Bijective
        (fun k : C ⟶ derivedInclusion.obj N => F ≫ k) from h) N
    rw [hfun N]
    exact (bijective_precomp_iso_hom u).comp hb

/-- `SolidEquiv` is invariant under postcomposition with the inverse of an isomorphism. -/
lemma solidEquiv_of_iso_right {B C D : DLightCondAb} (v : C ≅ D) (F : B ⟶ D) :
    Submission.Blueprint.SolidEquiv (F ≫ v.inv) ↔ Submission.Blueprint.SolidEquiv F := by
  have hfun : ∀ N : DSolid,
      (fun k : C ⟶ derivedInclusion.obj N => (F ≫ v.inv) ≫ k) =
        (fun m : D ⟶ derivedInclusion.obj N => F ≫ m) ∘
          (fun k : C ⟶ derivedInclusion.obj N => v.inv ≫ k) := by
    intro N
    funext k
    simp only [Function.comp_apply, Category.assoc]
  constructor
  · intro h
    intro N
    have hb : Function.Bijective
        (fun k : C ⟶ derivedInclusion.obj N => (F ≫ v.inv) ≫ k) :=
      (show ∀ N : DSolid, Function.Bijective
        (fun k : C ⟶ derivedInclusion.obj N => (F ≫ v.inv) ≫ k) from h) N
    rw [hfun N] at hb
    exact (Function.Bijective.of_comp_iff (fun m : D ⟶ derivedInclusion.obj N => F ≫ m)
      (bijective_precomp_iso_inv v)).mp hb
  · intro h
    intro N
    have hb : Function.Bijective (fun m : D ⟶ derivedInclusion.obj N => F ≫ m) :=
      (show ∀ N : DSolid, Function.Bijective
        (fun m : D ⟶ derivedInclusion.obj N => F ≫ m) from h) N
    rw [hfun N]
    exact hb.comp (bijective_precomp_iso_inv v)

/-- `SolidEquiv` is invariant under conjugation by isomorphisms of source and target. -/
lemma solidEquiv_comp_iso {A B C D : DLightCondAb} (u : A ≅ B) (v : C ≅ D) (F : B ⟶ D) :
    Submission.Blueprint.SolidEquiv (u.hom ≫ F ≫ v.inv) ↔
      Submission.Blueprint.SolidEquiv F :=
  (solidEquiv_of_iso_left u (F ≫ v.inv)).trans (solidEquiv_of_iso_right v F)

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- **AN5 transported to light condensed sets.**  For a light profinite set `S`, the projection
`prodProj (lc S) : lc S ⊗ Icond ⟶ lc S` (`prodProj X = X ◁ toUnit Icond ≫ (ρ_ X).hom`, the first
projection of the product with the interval, where `lc = lightProfiniteToLightCondSet`) is a
solid-equivalence after applying `free ℤ` and `singleFunctor LightCondAb 0`.

Route: `Work.ANALYTIC.profinite_HI S` gives the solid-equivalence of
`freeLightCondAbOfTopFunctor.map (prTop S.toTopCat)`, i.e. of `free ℤ` applied to
`topCatToLightCondSet.map (prTop S.toTopCat) : T (S × [0,1]) ⟶ T S`.  Now
`freeLightCondAbOfTopFunctor = topCatToLightCondSet ⋙ free ℤ` is strong monoidal
(`Work.ANALYTIC.instMonoidalTopCatToLightCondSet`, cartesian structure) and
`prTop S.toTopCat = SemiCartesianMonoidalCategory.fst (S.toTopCat) unitIntervalTopCat`
(`Work.ANALYTIC.prTop_eq_fst`), whose transport along the tensorators is exactly
`prodProj (lc S)` conjugated by the canonical isomorphisms
`lc S ≅ topCatToLightCondSet.obj S.toTopCat`
(`Mathlib: lightProfiniteToLightCondSetIsoTopCatToLightCondSet`) and
`Icond = topCatToLightCondSet.obj unitIntervalTopCat`.  Conclude by two-out-of-three
(`Work.ANALYTIC.toolkitProp.of_iso`, `of_comp_left`, `of_comp_right`). -/
theorem prodProj_lc_solidEquiv (S : LightProfinite.{0}) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((LightCondensed.free (R := ℤ)).map
          (Work.ANALYTIC.prodProj (lightProfiniteToLightCondSet.obj S)))) := by
  -- AN5: the topological projection `prTop S` is a solid-equivalence after `ℤ[-]`
  have h1 : Submission.Blueprint.SolidEquiv
      (Submission.Blueprint.dFree (prTop (LightProfinite.toTopCat.obj S))) :=
    profinite_HI S
  -- Step 1: transport along the tensorator of `topCatToLightCondSet`
  have h2 : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((LightCondensed.free (R := ℤ)).map
          (prodProj (topCatToLightCondSet.obj (LightProfinite.toTopCat.obj S))))) := by
    have key : ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
          ((LightCondensed.free (R := ℤ)).mapIso (Functor.Monoidal.μIso topCatToLightCondSet
            (LightProfinite.toTopCat.obj S) unitIntervalTopCat))).hom ≫
        Submission.Blueprint.dFree (prTop (LightProfinite.toTopCat.obj S)) =
        (DerivedCategory.singleFunctor LightCondAb 0).map
          ((LightCondensed.free (R := ℤ)).map
            (prodProj (topCatToLightCondSet.obj (LightProfinite.toTopCat.obj S)))) := by
      show (DerivedCategory.singleFunctor LightCondAb 0).map
          ((LightCondensed.free (R := ℤ)).map (Functor.Monoidal.μIso topCatToLightCondSet
            (LightProfinite.toTopCat.obj S) unitIntervalTopCat).hom) ≫
          (DerivedCategory.singleFunctor LightCondAb 0).map
            ((LightCondensed.free (R := ℤ)).map
              (topCatToLightCondSet.map (prTop (LightProfinite.toTopCat.obj S)))) =
        (DerivedCategory.singleFunctor LightCondAb 0).map
          ((LightCondensed.free (R := ℤ)).map
            (prodProj (topCatToLightCondSet.obj (LightProfinite.toTopCat.obj S))))
      rw [← Functor.map_comp, ← Functor.map_comp, muIso_hom_comp_map_prTop]
      rfl
    exact key ▸ (solidEquiv_of_iso_left
      ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
        ((LightCondensed.free (R := ℤ)).mapIso (Functor.Monoidal.μIso topCatToLightCondSet
          (LightProfinite.toTopCat.obj S) unitIntervalTopCat)))
      (Submission.Blueprint.dFree (prTop (LightProfinite.toTopCat.obj S)))).mpr h1
  -- Step 2: transport along the canonical isomorphism `lc S ≅ T S`
  let e := lightProfiniteToLightCondSetIsoTopCatToLightCondSet.app S
  have key3 :
      ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
          ((LightCondensed.free (R := ℤ)).mapIso (whiskerRightIso e Icond))).hom ≫
        (DerivedCategory.singleFunctor LightCondAb 0).map
          ((LightCondensed.free (R := ℤ)).map
            (prodProj (topCatToLightCondSet.obj (LightProfinite.toTopCat.obj S)))) ≫
        ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
          ((LightCondensed.free (R := ℤ)).mapIso e)).inv =
      (DerivedCategory.singleFunctor LightCondAb 0).map
        ((LightCondensed.free (R := ℤ)).map
          (prodProj (lightProfiniteToLightCondSet.obj S))) := by
    rw [Functor.mapIso_hom, Functor.mapIso_inv]
    simp only [← Functor.map_comp]
    congr 1
    rw [Functor.mapIso_hom, Functor.mapIso_inv]
    simp only [← Functor.map_comp]
    congr 1
  exact key3 ▸ (solidEquiv_comp_iso
    ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
      ((LightCondensed.free (R := ℤ)).mapIso (whiskerRightIso e Icond)))
    ((DerivedCategory.singleFunctor LightCondAb 0).mapIso
      ((LightCondensed.free (R := ℤ)).mapIso e))
    ((DerivedCategory.singleFunctor LightCondAb 0).map
      ((LightCondensed.free (R := ℤ)).map
        (prodProj (topCatToLightCondSet.obj (LightProfinite.toTopCat.obj S)))))).mpr h2

end

end Work.ANALYTIC
