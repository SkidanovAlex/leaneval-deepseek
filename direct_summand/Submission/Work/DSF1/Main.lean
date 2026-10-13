import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Setup
import Submission.Work.DSF1.Scheme.Affine
import Submission.Work.DSF1.Canonical
import Submission.Work.DSF1.Canonical.isIso_canonical_top
import Submission.Work.DSF1.Cech.cechTerm_acyclic
import Submission.Work.DSF1.Cech.cechSheafCoaug_quasiIso
import Submission.Work.DSF1.Derived.unit_compat_resolution
import Submission.Work.DSF1.Sheaf.secSheaf_acyclic_affineHom
import Submission.Work.DSF1.Sheaf.exists_cechSheafPresheaf
import Submission.Work.DSF1.Sheaf.AcyclicToolkit
import Submission.Work.DSEQ0.AugMain
import Submission.Work.DSEQ0.cechShZ_compat
import Submission.Work.DSEQ0.isIso_psiUnitHom
import Submission.Work.DSG1.rdfpuBridge
import Submission.Work.DSEQ0.termwise_acyclic_unit_iso

open CategoryTheory AlgebraicGeometry Limits

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace DSMap

universe a b c

/-- `Γ_A = Γ(X,-)` preserves finite limits. -/
lemma gammaA_preservesFiniteLimits (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) :
    Limits.PreservesFiniteLimits (GammaA A X f) := by
  have hE : Limits.PreservesFiniteLimits
      (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))) := inferInstance
  have hR : Limits.PreservesFiniteLimits.{a, a, a + 1, a + 1}
      (ModuleCat.restrictScalars.{a, a, a} (DSMap.phi A X f)) := inferInstance
  exact @Limits.comp_preservesFiniteLimits _ _ _ _ _ _
    (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens)))
    (ModuleCat.restrictScalars.{a, a, a} (DSMap.phi A X f)) hE hR

/-- A chain map out of the one-term complex `A[0]` is determined by its degree-`0` component. -/
lemma coaug_eq_of_coaugClause {A : Type a} [CommRing A] {X : Scheme.{a}} {f : X ⟶ Spec (.of A)}
    {ι : Type a} {U : ι → X.Opens}
    {cc cc' : (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ cechZ A X f U}
    (h : cc.f 0 ≫ ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        coaug0 A X f U)
    (h' : cc'.f 0 ≫ ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
        coaug0 A X f U) : cc = cc' := by
  set_option backward.isDefEq.respectTransparency false in
  have h0 : cc.f 0 = cc'.f 0 := by
    haveI : IsIso ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom :=
      Iso.isIso_hom _
    rw [← cancel_mono ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom]
    rw [h, h']
  refine HomologicalComplex.Hom.ext ?_
  funext i
  by_cases hi : i = 0
  · subst hi; exact h0
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of A A) i
      hi).eq_of_src _ _

end DSMap

namespace DSMap

set_option backward.isDefEq.respectTransparency false in
theorem area_F1_cech_proved.{a, b, c} (A : Type a) [CommRing A] [HasDerivedCategory.{b} (ModuleCat.{a} A)]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] [IsSeparated f] [QuasiCompact f]
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∃ (cc : (HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A) ⟶ cechZ A X f U)
      (e : DerivedCategory.Plus.ι.obj (RG A X f) ≅ DerivedCategory.Q.obj (cechZ A X f U)),
      cc.f 0 ≫ ((cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
            coaug0 A X f U ∧
      DerivedCategory.Plus.ι.map (rgUnit A X f) ≫ e.hom =
        (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{a} A) 0).hom.app _ ≫
          (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{a} A) 0).hom.app _ ≫
            DerivedCategory.Q.map cc := by
  classical
  have hAdd : (ModuleCat.restrictScalars.{a, a, a} (DSMap.phi A X f)).Additive := inferInstance
  have hPH : (ModuleCat.restrictScalars.{a, a, a} (DSMap.phi A X f)).PreservesHomology :=
    inferInstance
  let K : CochainComplex (SheafOfModules X.ringCatSheaf) ℕ :=
    (cechComplexFunctor U).obj (Work.DSF1.Sheaf.cechSheafPresheaf X)
  haveI hKi : CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let Kp : CochainComplex.Plus (SheafOfModules X.ringCatSheaf) :=
    ⟨K.extend ComplexShape.embeddingUpNat, ⟨0, hKi⟩⟩
  have hacycTop : ∀ (W : X.Opens), IsAffineOpen W → IsAffineHom (Scheme.Opens.ι W) →
      ∀ q : ℕ, 0 < q →
        IsZero (((Work.DSF1.Sheaf.gammaTop X).rightDerived q).obj (Work.DSF1.secSheaf W)) := by
    intro W hW hHom q hq
    letI : HasDerivedCategory (ModuleCat.{a, a} (X.ringCatSheaf.obj.obj (Opposite.op
      (⊤ : X.Opens)))) := HasDerivedCategory.standard _
    exact Work.DSF1.Sheaf.isZero_rightDerived_secSheaf X W hW hHom q hq
  have hacyc : ∀ (W : X.Opens), IsAffineOpen W → IsAffineHom (Scheme.Opens.ι W) →
      ∀ q : ℕ, 0 < q → IsZero (((GammaA A X f).rightDerived q).obj (Work.DSF1.secSheaf W)) := by
    intro W hW hHom q hq
    letI : HasDerivedCategory (ModuleCat.{a, a} (X.ringCatSheaf.obj.obj (Opposite.op
      (⊤ : X.Opens)))) := HasDerivedCategory.standard _
    obtain ⟨e⟩ := @Work.DSF1.Sheaf.rightDerived_comp_exact _ _ _ _ _ _ _ _ _ _ _
      (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))) _
      (ModuleCat.restrictScalars.{a, a, a} (DSMap.phi A X f)) hAdd hPH
      (Work.DSF1.secSheaf W) q
    exact IsZero.of_iso
      (Functor.map_isZero (ModuleCat.restrictScalars.{a, a, a} (DSMap.phi A X f))
        (hacycTop W hW hHom q hq)) e
  have hac : ∀ n k : ℕ, 0 < k → IsZero (((GammaA A X f).rightDerived k).obj (K.X n)) :=
    fun n k hk => Work.DSF1.Cech.cechTerm_acyclic X f U hU (by rw [sSup_range]; exact hcov)
      hacyc k hk n
  have hKac : ∀ (i : ℤ) (k : ℕ), 0 < k →
      IsZero (((GammaA A X f).rightDerived k).obj (Kp.obj.X i)) := by
    intro i k hk
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    by_cases hi : i < 0
    · haveI : Injective (Kp.obj.X i) :=
        (CochainComplex.isZero_of_isStrictlyGE
          (K.extend ComplexShape.embeddingUpNat) 0 i hi).injective
      exact Functor.isZero_rightDerived_obj_injective_succ (GammaA A X f) m (Kp.obj.X i)
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
      exact IsZero.of_iso (hac j (m + 1) (by omega))
        (((GammaA A X f).rightDerived (m + 1)).mapIso (HomologicalComplex.extendXIso K
          ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f j = ((j : ℕ) : ℤ) from rfl)))
  haveI hPFL : Limits.PreservesFiniteLimits (GammaA A X f) :=
    gammaA_preservesFiniteLimits A X f
  haveI hunit : IsIso ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp) :=
    Work.DSEQ0.termwise_acyclic_unit_iso (GammaA A X f) Kp hKac
  -- ### the coaugmentation and the comparison
  have haug : Work.DSEQ0.aug0 X U ≫ (Work.DSEQ0.cechSh X U).d 0 1 = 0 :=
    Work.DSEQ0.C.aug0_comp_d X U
  obtain ⟨ψ, qc, hqc⟩ := Work.DSEQ0.cechShZ_compat A X f U haug
  let qZ : Work.DSF1.Sheaf.singlePlusObj (SheafOfModules X.ringCatSheaf)
      (Work.DSF1.secSheaf (⊤ : X.Opens)) ⟶ Kp :=
    ObjectProperty.homMk (Work.DSEQ0.augZ X U haug)
  haveI hqZ : IsIso ((DerivedCategory.Plus.Q).map qZ) := by
    refine Localization.inverts (DerivedCategory.Plus.Q) (CochainComplex.Plus.quasiIso _) qZ ?_
    exact (CochainComplex.Plus.quasiIso_iff _ qZ).2 (by
      change QuasiIso (Work.DSEQ0.C.augZ X U haug)
      exact Work.DSEQ0.C.quasiIso_augZ_of X U haug
        (by
          rw [Work.DSF1.Cech.augN_eq_cechSheafCoaug U haug]
          exact Work.DSF1.Cech.cechSheafCoaug_quasiIso U (by rw [sSup_range]; exact hcov)))
  let ψP : Work.DSF1.Sheaf.singlePlusObj (SheafOfModules X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) ≅
      Work.DSF1.Sheaf.singlePlusObj (SheafOfModules X.ringCatSheaf)
        (Work.DSF1.secSheaf (⊤ : X.Opens)) :=
    ObjectProperty.isoMk _
      ((CochainComplex.singleFunctor (SheafOfModules X.ringCatSheaf) 0).mapIso ψ)
  let qM : Work.DSF1.Sheaf.singlePlusObj (SheafOfModules X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) ⟶ Kp := ψP.hom ≫ qZ
  let qMi : (DerivedCategory.Plus.Q).obj (Work.DSF1.Sheaf.singlePlusObj
        (SheafOfModules X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)) ≅
      (DerivedCategory.Plus.Q).obj Kp :=
    (DerivedCategory.Plus.Q).mapIso ψP ≪≫ asIso ((DerivedCategory.Plus.Q).map qZ)
  have hqM : (DerivedCategory.Plus.Q).map qM = qMi.hom := by
    rw [show qM = ψP.hom ≫ qZ from rfl, CategoryTheory.Functor.map_comp]
    rfl
  -- ### the isomorphism
  let e1 : RG A X f ≅
      (DerivedCategory.Plus.Q).obj ((GammaA A X f).mapCochainComplexPlus.obj Kp) :=
    (GammaA A X f).rightDerivedFunctorPlus.mapIso qMi ≪≫
      (asIso ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp)).symm
  let e : DerivedCategory.Plus.ι.obj (RG A X f) ≅ DerivedCategory.Q.obj (cechZ A X f U) :=
    DerivedCategory.Plus.ι.mapIso e1 ≪≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{a} A)).app
        ((GammaA A X f).mapCochainComplexPlus.obj Kp) ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapCochainComplexPlusCompι (GammaA A X f)).app Kp) ≪≫
      DerivedCategory.Q.mapIso qc
  -- ### the chain-map identity
  have hccZ : Work.DSEQ0.cechZCompatMap (X := X) (A := A) (f := f) (U := U) ψ haug qc.hom = Work.DSF1.ccZ A X f U :=
    coaug_eq_of_coaugClause (X := X) (f := f) (U := U) hqc
      (Work.DSF1.ccZ_compat A X f U)
  -- ### the compatibility with the unit
  have hqMhom : qM.hom = Work.DSEQ0.augZTop X U ψ haug := rfl
  have hmapinv : ((Work.DSG1.mapSinglePlusIso (GammaA A X f)
        (SheafOfModules.unit X.ringCatSheaf))).inv.hom =
      ((HomologicalComplex.singleMapHomologicalComplex (GammaA A X f) (ComplexShape.up ℤ) 0).app
        (SheafOfModules.unit X.ringCatSheaf)).inv := by
    have h1 : (CochainComplex.Plus.ι (ModuleCat.{a} A)).mapIso
        (Work.DSG1.mapSinglePlusIso (GammaA A X f) (SheafOfModules.unit X.ringCatSheaf)) =
        (Functor.mapCochainComplexPlusCompι (GammaA A X f)).app
            (Work.DSF1.Sheaf.singlePlusObj (SheafOfModules X.ringCatSheaf)
              (SheafOfModules.unit X.ringCatSheaf)) ≪≫
          (HomologicalComplex.singleMapHomologicalComplex (GammaA A X f) (ComplexShape.up ℤ) 0).app
            (SheafOfModules.unit X.ringCatSheaf) := by
      rw [Work.DSG1.mapSinglePlusIso]
      apply Iso.ext
      rw [Functor.mapIso_hom, Functor.FullyFaithful.preimageIso_hom]
      exact Functor.FullyFaithful.map_preimage _ _
    have h2 : ((Work.DSG1.mapSinglePlusIso (GammaA A X f)
          (SheafOfModules.unit X.ringCatSheaf))).inv.hom =
        ((CochainComplex.Plus.ι (ModuleCat.{a} A)).mapIso
          (Work.DSG1.mapSinglePlusIso (GammaA A X f)
            (SheafOfModules.unit X.ringCatSheaf))).inv := rfl
    rw [h2, h1]
    erw [Iso.trans_inv]
  have hbeta : ((Work.DSG1.mapSinglePlusIso (GammaA A X f)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (GammaA A X f).mapCochainComplexPlus.map qM).hom =
      ((HomologicalComplex.singleMapHomologicalComplex (GammaA A X f) (ComplexShape.up ℤ) 0).inv.app
        (SheafOfModules.unit X.ringCatSheaf)) ≫
      ((GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Work.DSEQ0.augZTop X U ψ haug) := by
    rw [show ((Work.DSG1.mapSinglePlusIso (GammaA A X f)
          (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (GammaA A X f).mapCochainComplexPlus.map qM).hom =
        ((Work.DSG1.mapSinglePlusIso (GammaA A X f)
          (SheafOfModules.unit X.ringCatSheaf))).inv.hom ≫
        ((GammaA A X f).mapCochainComplexPlus.map qM).hom from rfl]
    rw [hmapinv]
    rw [show ((GammaA A X f).mapCochainComplexPlus.map qM).hom =
        ((GammaA A X f).mapHomologicalComplex (ComplexShape.up ℤ)).map qM.hom from rfl]
    rw [hqMhom]
    rfl
  have he1 : e1.hom = (GammaA A X f).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map qM) ≫
      CategoryTheory.inv ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp) := by
    rw [show e1.hom = (GammaA A X f).rightDerivedFunctorPlus.map qMi.hom ≫
        CategoryTheory.inv ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp) from rfl]
    rw [← hqM]
  have hbase : DerivedCategory.Plus.ι.map
        ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
          (SheafOfModules.unit X.ringCatSheaf)) ≫
      DerivedCategory.Plus.ι.map e1.hom =
      DerivedCategory.Q.map (((Work.DSG1.mapSinglePlusIso (GammaA A X f)
          (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (GammaA A X f).mapCochainComplexPlus.map qM).hom) := by
    have huc := Work.DSF1.Derived.unit_compat_resolution (GammaA A X f)
      (SheafOfModules.unit X.ringCatSheaf) Kp qM hunit
    rw [Category.assoc] at huc
    erw [he1]
    erw [show DerivedCategory.Plus.ι.map
          ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        DerivedCategory.Plus.ι.map
          ((GammaA A X f).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map qM) ≫
            CategoryTheory.inv ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp)) =
      DerivedCategory.Plus.ι.map
        ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (GammaA A X f).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map qM) ≫
            CategoryTheory.inv ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp)) from
      (CategoryTheory.Functor.map_comp DerivedCategory.Plus.ι
        ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
          (SheafOfModules.unit X.ringCatSheaf))
        ((GammaA A X f).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map qM) ≫
          CategoryTheory.inv ((GammaA A X f).rightDerivedFunctorPlusUnit.app Kp))).symm]
    erw [huc]
    rw [Functor.mapIso_hom]
    erw [← CategoryTheory.Functor.map_comp (self := DerivedCategory.Plus.Q)
      (f := ((Work.DSG1.mapSinglePlusIso (GammaA A X f)
        (SheafOfModules.unit X.ringCatSheaf)).symm).hom)
      (g := (GammaA A X f).mapCochainComplexPlus.map qM)]
    rw [show (((Work.DSG1.mapSinglePlusIso (GammaA A X f)
          (SheafOfModules.unit X.ringCatSheaf)).symm).hom) =
        (Work.DSG1.mapSinglePlusIso (GammaA A X f)
          (SheafOfModules.unit X.ringCatSheaf)).inv from
      Iso.symm_hom _]
    rfl
  have hfinal : DerivedCategory.Plus.ι.map (rgUnit A X f) ≫ e.hom =
      DerivedCategory.Q.map (Work.DSF1.ccZ A X f U) := by
    have hdec : DerivedCategory.Plus.ι.map (rgUnit A X f) =
        DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{a} A) (ComplexShape.up ℤ) 0).map
          (letI : Algebra A (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) :=
            (DSMap.phi A X f).toAlgebra
           ModuleCat.ofHom (Algebra.linearMap A (X.presheaf.obj (Opposite.op (⊤ : X.Opens)))))) ≫
        DerivedCategory.Plus.ι.map
          ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
            (SheafOfModules.unit X.ringCatSheaf)) := rfl
    have he : e.hom = DerivedCategory.Plus.ι.map e1.hom ≫ DerivedCategory.Q.map qc.hom := by
      have h2 : (DerivedCategory.Plus.ι.mapIso e1 ≪≫
            (DerivedCategory.Plus.QCompιIso (ModuleCat.{a} A)).app
              ((GammaA A X f).mapCochainComplexPlus.obj Kp) ≪≫
            DerivedCategory.Q.mapIso ((Functor.mapCochainComplexPlusCompι (GammaA A X f)).app Kp) ≪≫
            DerivedCategory.Q.mapIso qc).hom =
          DerivedCategory.Plus.ι.map e1.hom ≫ DerivedCategory.Q.map qc.hom := by
        have hA : (DerivedCategory.Plus.QCompιIso (ModuleCat.{a} A)).app
              ((GammaA A X f).mapCochainComplexPlus.obj Kp) = Iso.refl _ := rfl
        have hB : (Functor.mapCochainComplexPlusCompι (GammaA A X f)).app Kp = Iso.refl _ := rfl
        rw [hA, hB]
        simp only [Iso.trans_hom, Iso.refl_hom, Functor.mapIso_hom]
        rw [show DerivedCategory.Q.map (𝟙 (((GammaA A X f).mapCochainComplexPlus ⋙
            CochainComplex.Plus.ι (ModuleCat.{a} A)).obj Kp)) = 𝟙 _ from
          CategoryTheory.Functor.map_id _ _]
        erw [Category.id_comp, Category.id_comp]
      rw [show e.hom = (DerivedCategory.Plus.ι.mapIso e1 ≪≫
            (DerivedCategory.Plus.QCompιIso (ModuleCat.{a} A)).app
              ((GammaA A X f).mapCochainComplexPlus.obj Kp) ≪≫
            DerivedCategory.Q.mapIso ((Functor.mapCochainComplexPlusCompι (GammaA A X f)).app Kp) ≪≫
            DerivedCategory.Q.mapIso qc).hom from rfl]
      exact h2
    have hbaseY : DerivedCategory.Plus.ι.map
          ((LeanEval.AlgebraicGeometry.DirectSummand.rightDerivedFunctorPlusUnit' (GammaA A X f) 0).app
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        DerivedCategory.Plus.ι.map e1.hom ≫ DerivedCategory.Q.map qc.hom =
        DerivedCategory.Q.map (((Work.DSG1.mapSinglePlusIso (GammaA A X f)
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (GammaA A X f).mapCochainComplexPlus.map qM).hom) ≫
          DerivedCategory.Q.map qc.hom := by
      rw [← Category.assoc]
      rw [hbase]
    rw [hdec, he]
    simp only [Category.assoc]
    rw [hbaseY]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rw [hbeta, ← hccZ]
    rfl
  refine ⟨Work.DSF1.ccZ A X f U, e, Work.DSF1.ccZ_compat A X f U, ?_⟩
  show DerivedCategory.Plus.ι.map (rgUnit A X f) ≫ e.hom =
      (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{a} A) 0).hom.app (ModuleCat.of A A) ≫
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{a} A) 0).hom.app (ModuleCat.of A A) ≫
          DerivedCategory.Q.map (Work.DSF1.ccZ A X f U)
  rw [show (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{a} A) 0).hom.app (ModuleCat.of A A)
        = 𝟙 _ from Iso.refl_hom _]
  rw [show (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{a} A) 0).hom.app (ModuleCat.of A A)
        = 𝟙 _ from Iso.refl_hom _]
  erw [Category.id_comp, Category.id_comp]
  exact hfinal

end DSMap

/-! ## Machine-checked consistency with the frozen interface -/

/-- The type of the deliverable is definitionally identical to the type of the frozen
`DSMap.area_F1_cech`.  (Universe levels are made explicit: without them `type_of%` introduces
two distinct level metavariables and `rfl` is not applicable.) -/
example : type_of% (@DSMap.area_F1_cech_proved.{0, 0, 0}) =
    type_of% (@DSMap.area_F1_cech.{0, 0, 0}) := rfl

-- Axiom check: the theorem uses no axioms beyond the three standard ones (in particular it is
-- free of placeholders).
#print axioms DSMap.area_F1_cech_proved
