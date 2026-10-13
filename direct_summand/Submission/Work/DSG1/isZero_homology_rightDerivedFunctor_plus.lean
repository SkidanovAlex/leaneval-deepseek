import Mathlib

set_option linter.style.haveILetI false

namespace Work.DSG1

open CategoryTheory Limits

/-- The `q`-th homology of the image `DerivedCategory.Plus.Q.obj K` of a bounded-below complex `K`
in the bounded-below derived category is the `q`-th homology of `K`.

This is the composite of the image under `DerivedCategory.homologyFunctor C q` of the structural
isomorphism `DerivedCategory.Plus.QCompιIso C` (at the object `K`) with the structural isomorphism
`DerivedCategory.homologyFunctorFactors C q`. -/
noncomputable def homologyFunctor_Q_obj_iso_aux {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C q).obj (DerivedCategory.Plus.Q.obj K) ≅
      K.obj.homology q :=
  (DerivedCategory.homologyFunctor C q).mapIso ((DerivedCategory.Plus.QCompιIso C).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors C q).app ((CochainComplex.Plus.ι C).obj K)

/-- If a bounded below cochain complex `K` has vanishing cohomology in degrees `< n`, then the same
holds for `R⁺F` of `K`, for any additive functor between abelian categories with enough injectives
in the source. -/
theorem isZero_homology_rightDerivedFunctor_plus {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D)
    [F.Additive] [EnoughInjectives C] (K : CochainComplex.Plus C) (n j : ℤ)
    (hK : K.obj.IsGE n) (hj : j < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D j).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) := by
  -- The image of `K` in the bounded below derived category is cohomologically `≥ n`.
  haveI hQK : (DerivedCategory.Plus.Q.obj K).IsGE n := by
    haveI h1 : DerivedCategory.TStructure.t.IsGE
        ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q).obj K) n := by
      change (DerivedCategory.Q.obj K.obj).IsGE n
      rw [DerivedCategory.isGE_Q_obj_iff]
      exact hK
    have h2 : (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)).IsGE n :=
      DerivedCategory.TStructure.t.isGE_of_iso ((DerivedCategory.Plus.QCompιIso C).app K).symm n
    rwa [DerivedCategory.Plus.isGE_ι_obj_iff] at h2
  -- Resolve it by a complex of injective objects that is strictly supported in degrees `≥ n`.
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso
    (DerivedCategory.Plus.Q.obj K) n
  let X : CochainComplex.Plus C := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  -- The unit of the right derived functor is an isomorphism on `X`.
  have hη : IsIso (F.rightDerivedFunctorPlusUnit.app X) := by
    dsimp only [X]
    infer_instance
  -- `X` is strictly supported in degrees `≥ n`; so is `F` applied to it degreewise.
  haveI hX0 : X.obj.IsStrictlyGE n := by
    dsimp only [X]
    rw [Functor.mapCochainComplexPlus_obj_obj]
    haveI := hL
    infer_instance
  haveI hX : ((F.mapCochainComplexPlus.obj X).obj).IsStrictlyGE n := by
    rw [Functor.mapCochainComplexPlus_obj_obj]
    infer_instance
  -- Assemble the isomorphism `R⁺F (Q K) ≅ Q (F (X))` in the bounded below derived category.
  let Φ : (DerivedCategory.Plus.homologyFunctor D j).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      ((F.mapCochainComplexPlus.obj X).obj).homology j :=
    (DerivedCategory.Plus.homologyFunctor D j).mapIso
        (F.rightDerivedFunctorPlus.mapIso e.symm ≪≫
          (asIso (F.rightDerivedFunctorPlusUnit.app X)).symm) ≪≫
      homologyFunctor_Q_obj_iso_aux (F.mapCochainComplexPlus.obj X) j
  exact IsZero.of_iso
    (CochainComplex.isZero_of_isGE (F.mapCochainComplexPlus.obj X).obj n j hj) Φ

end Work.DSG1
