import Mathlib
import Submission.Work.DSF1.Sheaf.rightDerived_isZero_of_acyclic_resolution
import Submission.Work.DSF1.Sheaf.rightDerived_iso_plusHomology
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat
import Submission.Work.DSF1.Sheaf.AcyclicToolkit
import Submission.Work.DSEQ0.termwise_acyclic_unit_iso

namespace Work.DSF1.Sheaf

universe u v w x

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

/-- **The right derived functor computed by an acyclic resolution.**

If `F : C ⥤ D` is additive and left exact, `C` has enough injectives, `K` is an `ℕ`-indexed
cochain complex of `F`-acyclic objects together with a quasi-isomorphism
`q : M[0] ⟶ K`, then the `n`-th right derived functor of `F` at `M` is the `n`-th homology of
the complex `F K` obtained by applying `F` degreewise.

The proof is the classical one.  Both `M[0]` and `K` (extended by zero to `ℤ`) are bounded below
cochain complexes; `q` gives a quasi-isomorphism between them, so `R⁺F` of the two derived
objects agree; because every term of `K` is `F`-acyclic, the unit of the right derived functor is
an isomorphism at `K` (`Work.DSEQ0.termwise_acyclic_unit_iso`), whence
`R⁺F (Q K) ≅ Q (F K)`; homology of `Q` of a cochain complex is the homology of that complex
(`DerivedCategory.homologyFunctorFactors`); and the homology of the `ℤ`-indexed extension is the
homology of the original `ℕ`-indexed complex (`HomologicalComplex.extendHomologyIso`, together
with `mapHomologicalComplex_extendUpNat`).  The bridge between `R^n F (M)` and
`H^n (R⁺F (M[0]))` is `Work.DSF1.Sheaf.rightDerived_iso_plusHomology`. -/
theorem rightDerived_iso_homology_of_acyclic_resolution {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] (M : C) (K : CochainComplex C ℕ)
    [∀ i : ℕ, HomologicalComplex.HasHomology K i]
    (q : (CochainComplex.single₀ C).obj M ⟶ K) [QuasiIso q]
    (hac : ∀ n k : ℕ, 0 < k → CategoryTheory.Limits.IsZero ((F.rightDerived k).obj (K.X n)))
    (n : ℕ) :
    Nonempty ((F.rightDerived n).obj M ≅
      HomologicalComplex.homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n) := by
  classical
  haveI : HasDerivedCategory C := HasDerivedCategory.standard C
  haveI : HasDerivedCategory D := HasDerivedCategory.standard D
  -- the `ℤ`-indexed extension of `K`, which is bounded below
  haveI hKi : CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 :=
    inferInstance
  let Kp : CochainComplex.Plus C := ⟨K.extend ComplexShape.embeddingUpNat, ⟨0, hKi⟩⟩
  let S : CochainComplex.Plus C := singlePlusObj C M
  let RF := F.rightDerivedFunctorPlus
  let Hd := DerivedCategory.Plus.homologyFunctor D (n : ℤ)
  -- the quasi-isomorphism `M[0] ⟶ K`, as a morphism of bounded below complexes
  let qZ : S ⟶ Kp := ObjectProperty.homMk
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv ≫
      HomologicalComplex.extendMap q ComplexShape.embeddingUpNat)
  have hqZ : IsIso ((DerivedCategory.Plus.Q).map qZ) := by
    refine Localization.inverts (DerivedCategory.Plus.Q) (CochainComplex.Plus.quasiIso C) qZ ?_
    exact (CochainComplex.Plus.quasiIso_iff C qZ).2 (by
      change QuasiIso ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0
        rfl).inv ≫ HomologicalComplex.extendMap q ComplexShape.embeddingUpNat)
      infer_instance)
  -- the canonical isomorphism `M[0] ≅ Q S`
  have eA : (DerivedCategory.Plus.singleFunctor C 0).obj M ≅
      (DerivedCategory.Plus.Q).obj S :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app M ≪≫
        (DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app S).symm)
  -- the terms of `K` are `F`-acyclic, hence the unit of `R⁺F` is an isomorphism at `K`
  have hKac : ∀ (i : ℤ) (k : ℕ), 0 < k → IsZero ((F.rightDerived k).obj (Kp.obj.X i)) := by
    intro i k hk
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    by_cases hi : i < 0
    · haveI : Injective (Kp.obj.X i) :=
        (CochainComplex.isZero_of_isStrictlyGE
          (K.extend ComplexShape.embeddingUpNat) 0 i hi).injective
      exact Functor.isZero_rightDerived_obj_injective_succ F m (Kp.obj.X i)
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
      exact IsZero.of_iso (hac j (m + 1) (by omega))
        ((F.rightDerived (m + 1)).mapIso (HomologicalComplex.extendXIso K
          ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f j = ((j : ℕ) : ℤ) from rfl)))
  haveI hunit : IsIso (F.rightDerivedFunctorPlusUnit.app Kp) :=
    Work.DSEQ0.termwise_acyclic_unit_iso F Kp hKac
  -- homology of `Q` of a complex is the homology of the complex
  have step5 : Hd.obj ((DerivedCategory.Plus.Q).obj ((F.mapCochainComplexPlus).obj Kp)) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
        (((F.mapCochainComplexPlus).obj Kp).obj) :=
    (DerivedCategory.homologyFunctor D (n : ℤ)).mapIso
        ((DerivedCategory.Plus.QCompιIso D).app ((F.mapCochainComplexPlus).obj Kp)) ≪≫
      (DerivedCategory.homologyFunctorFactors D (n : ℤ)).app
        ((F.mapCochainComplexPlus).obj Kp).obj
  -- passing from the `ℤ`-indexed extension to the `ℕ`-indexed complex
  obtain ⟨eK⟩ := mapHomologicalComplex_extendUpNat F K
  have step6 : (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).obj
        (((F.mapCochainComplexPlus).obj Kp).obj) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).mapIso eK ≪≫
      HomologicalComplex.extendHomologyIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = ((n : ℕ) : ℤ) from rfl)
  obtain ⟨br⟩ := rightDerived_iso_plusHomology F M n
  refine ⟨br ≪≫ Hd.mapIso (RF.mapIso (eA ≪≫ asIso ((DerivedCategory.Plus.Q).map qZ))) ≪≫
    Hd.mapIso (asIso (F.rightDerivedFunctorPlusUnit.app Kp)).symm ≪≫ step5 ≪≫ step6 ≪≫ ?_⟩
  exact eqToIso (HomologicalComplex.homologyFunctor_obj D (ComplexShape.up ℕ) n
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))

end Work.DSF1.Sheaf
