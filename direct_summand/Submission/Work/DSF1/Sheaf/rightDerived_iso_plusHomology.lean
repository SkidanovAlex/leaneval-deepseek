import Mathlib
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat

/-!
# The classical right derived functors as the homology of the right derived functor

For an additive functor `F : C ⥤ D` between abelian categories where `C` has enough
injectives, the `n`-th right derived functor `F.rightDerived n` of `F` (defined on `C`
by means of injective resolutions) computes the `n`-th homology of the right derived
functor `F.rightDerivedFunctorPlus` on the bounded below derived category applied to
the one-term complex `A[0]`.

The proof goes through an injective resolution `R` of `A`:

* `(F.rightDerived n).obj A ≅ H^n(F(R.cocomplex))` (Mathlib's
  `InjectiveResolution.isoRightDerivedObj`), where `R.cocomplex` is indexed by `ℕ`;
* this homology is the homology in degree `n` of the `ℤ`-indexed complex
  `R.cochainComplex = R.cocomplex.extend embeddingUpNat` after applying `F`
  (Mathlib's `HomologicalComplex.extendHomologyIso`, together with our lemma
  `mapHomologicalComplex_extendUpNat` which identifies `F` applied to the extension
  with the extension of `F` applied);
* in the bounded below derived category, `A[0]` and the resolution `R.cochainComplex`
  are quasi-isomorphic, and the right derived functor unit is an isomorphism on
  `R.cochainComplex` because all its terms are injective, so
  `RF(A[0]) ≅ RF(R.cochainComplex) ≅ F(R.cochainComplex)`;
* finally homology in the derived category is computed by homology of cochain
  complexes (`DerivedCategory.homologyFunctorFactors`).
-/

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

universe u v w x

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem rightDerived_iso_plusHomology {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : CategoryTheory.Functor C D) [F.Additive] (A : C) (n : ℕ) :
    Nonempty ((F.rightDerived n).obj A ≅
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
        ((F.rightDerivedFunctorPlus).obj
          ((DerivedCategory.Plus.singleFunctor C 0).obj A))) := by
  classical
  refine ⟨?_⟩
  -- the chosen injective resolution of `A` and the associated `ℕ`- and `ℤ`-indexed complexes
  let R : InjectiveResolution A := injectiveResolution A
  let M : CochainComplex C ℕ := R.cocomplex
  let Sc : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, ⟨0, inferInstance⟩⟩
  let Kc : CochainComplex.Plus C := ⟨R.cochainComplex, ⟨0, inferInstance⟩⟩
  let Qc := DerivedCategory.Plus.Q (C := C)
  let RF := F.rightDerivedFunctorPlus
  let Hd : DerivedCategory.Plus D ⥤ D :=
    DerivedCategory.Plus.homologyFunctor D (n : ℤ)
  let e := ComplexShape.embeddingUpNat
  -- step 1: the `n`-th right derived functor computed on an injective resolution
  have step1 : (F.rightDerived n).obj A ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M) :=
    R.isoRightDerivedObj F n
  -- step 2: passing from the `ℕ`-indexed to the `ℤ`-indexed homology
  have step2 : (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M).extend e) :=
    (HomologicalComplex.extendHomologyIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M)
      e (show e.f n = (n : ℤ) from rfl)).symm
  -- step 3: `F` applied to the extension is the extension of `F` applied
  have step3 : (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M).extend e) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (M.extend e)) :=
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (Classical.choice (mapHomologicalComplex_extendUpNat F M)).symm
  -- step 5: homology in the derived category is homology of cochain complexes
  have step5 : Hd.obj ((DerivedCategory.Plus.Q).obj ((F.mapCochainComplexPlus).obj Kc)) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
        (((F.mapCochainComplexPlus).obj Kc).obj) :=
    (DerivedCategory.homologyFunctor D (n : ℤ)).mapIso
        ((DerivedCategory.Plus.QCompιIso D).app ((F.mapCochainComplexPlus).obj Kc)) ≪≫
      (DerivedCategory.homologyFunctorFactors D (n : ℤ)).app
        ((F.mapCochainComplexPlus).obj Kc).obj
  -- the augmentation `A[0] ⟶ R.cochainComplex` is a quasi-isomorphism
  let i : Sc ⟶ Kc := ObjectProperty.homMk R.ι'
  have hqi : CochainComplex.Plus.quasiIso C i :=
    (CochainComplex.Plus.quasiIso_iff C i).2
      (by rw [show i.hom = R.ι' from rfl]; infer_instance)
  -- the unit of the right derived functor is an isomorphism at `R.cochainComplex`
  have hunit : IsIso (F.rightDerivedFunctorPlusUnit.app Kc) := by
    rw [F.rightDerivedFunctorPlusUnit_app]
    infer_instance
  have hmap : IsIso (Qc.map i) :=
    Localization.inverts Qc (CochainComplex.Plus.quasiIso C) _ hqi
  -- `A[0]` in the bounded below derived category is the image of the one-term complex
  have eA : (DerivedCategory.Plus.singleFunctor C 0).obj A ≅ Qc.obj Sc :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app A ≪≫
        (DerivedCategory.singleFunctorIsoCompQ C 0).app A ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app Sc).symm)
  exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step5.symm ≪≫
    Hd.mapIso (asIso (F.rightDerivedFunctorPlusUnit.app Kc)) ≪≫
    Hd.mapIso (RF.mapIso (asIso (Qc.map i)).symm) ≪≫
    Hd.mapIso (RF.mapIso eA.symm)

end Work.DSF1.Sheaf
