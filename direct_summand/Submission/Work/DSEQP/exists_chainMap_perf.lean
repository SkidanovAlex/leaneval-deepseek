import Mathlib
import Submission.Work.DSEQP.PerfAcyclic
import Submission.Work.DSMap.Mix2Fix
import Submission.Work.DSEQP.PerfChainAux
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSEQP.cechRestrictScalarsIso_hom_f
import Submission.Work.DSEQP.perf_unitTop_unitNat_eKfam
import Submission.Work.DSEQP.extendXIso_cancel_inv

namespace Work.DSEQP

universe u

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry Limits Opposite

theorem exists_chainMap_perf (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : DSMap.Mix2.IsFinFreeModelU A X f U P ε) :
    ∃ ρ : P ⟶ ((ModuleCat.restrictScalars (S.ψW.comp (DSMap.phi A X f))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((S.K U).extend ComplexShape.embeddingUpNat),
      CategoryTheory.CategoryStruct.comp ε
          (CategoryTheory.CategoryStruct.comp (ρ.f 0)
            ((ModuleCat.restrictScalars (S.ψW.comp (DSMap.phi A X f))).map
              ((S.K U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom)) =
        CategoryTheory.CategoryStruct.comp (DSMap.Mix2.unitA (S.ψW.comp (DSMap.phi A X f)))
          ((ModuleCat.restrictScalars (S.ψW.comp (DSMap.phi A X f))).map (S.eK U)) := by
  classical
  obtain ⟨hPbdd, hP0, φ, hφqi, hφ⟩ := hP
  let ψ : A →+* S.W := S.ψW.comp (DSMap.phi A X f)
  let R : ModuleCat.{u} S.W ⥤ ModuleCat.{u} A := ModuleCat.restrictScalars ψ
  let Kc : CochainComplex (ModuleCat.{u} S.W) ℕ := S.K U
  let L : CochainComplex (ModuleCat.{u} A) ℕ := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj Kc
  let N : CochainComplex (ModuleCat.{u} A) ℕ := (cechComplexFunctor U).obj (S.perfPresheaf ⋙ R)
  let lIso : L ≅ N := cechRestrictScalarsIso ψ U S.perfPresheaf
  let ν : DSMap.cech A X f U ⟶ L := (cechComplexFunctor U).map S.unitNat ≫ lIso.inv
  let μ : DSMap.cechZ A X f U ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Kc.extend ComplexShape.embeddingUpNat) :=
    HomologicalComplex.extendMap ν ComplexShape.embeddingUpNat ≫
      (mapHomologicalComplexExtendUpNatIso R Kc).inv
  -- the component formula for the restriction-of-scalars Čech iso
  have hB : lIso.hom.f 0 = piComparison R (S.Kobj U 0) :=
    cechRestrictScalarsIso_hom_f ψ U S.perfPresheaf 0
  -- the level-`0` coaugmentation compatibility
  have hC : ∀ a : (PerfSetup.CechIdx U 0).I,
      DSMap.unitTop A X f ≫ (DSMap.cechPresheaf A X f).map (homOfLE le_top).op ≫
        S.unitNat.app (op (PerfSetup.CechOp U 0 a)) =
      DSMap.Mix2.unitA ψ ≫ R.map (S.eKfam U a) :=
    fun a => perf_unitTop_unitNat_eKfam S U a
  -- the degree-`0` cancellation
  have hE : ((L.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫
      (mapHomologicalComplexExtendUpNatIso R Kc).inv.f 0) ≫
      R.map ((Kc.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom) = 𝟙 (L.X 0) :=
    extendXIso_cancel_inv R Kc
  have hE' : (L.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫
      (mapHomologicalComplexExtendUpNatIso R Kc).inv.f 0 ≫
      R.map ((Kc.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom) = 𝟙 (L.X 0) := by
    rw [← Category.assoc]
    exact hE
  -- `lIso.inv.f 0` is the inverse of the product comparison
  have hpc : lIso.inv.f 0 ≫ piComparison R (S.Kobj U 0) = 𝟙 (N.X 0) := by
    rw [← hB, ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  -- the degree-`0` component of `μ`
  have hμ0 : μ.f 0 = ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
        (i := 0) rfl).hom ≫ ν.f 0 ≫ (L.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫
      (mapHomologicalComplexExtendUpNatIso R Kc).inv.f 0 := by
    dsimp only [μ]
    rw [HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f ν ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
    simp only [Category.assoc]
  have hμ0' : μ.f 0 ≫ R.map ((Kc.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom) =
      ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫
        ν.f 0 := by
    rw [hμ0, Category.assoc, Category.assoc, Category.assoc, hE', Category.comp_id]
  -- the coaugmentation square in degree `0`
  have hEK : R.map (S.eK U) ≫ piComparison R (S.Kobj U 0) =
      Pi.lift (fun a => R.map (S.eKfam U a)) := by
    have h1 : S.eK U = Pi.lift (S.eKfam U) := rfl
    rw [h1]
    exact map_lift_piComparison R (S.Kobj U 0) (ModuleCat.of S.W S.W) (S.eKfam U)
  have hmain : DSMap.coaug0 A X f U ≫ ((cechComplexFunctor U).map S.unitNat).f 0 =
      DSMap.Mix2.unitA ψ ≫ Pi.lift (fun a => R.map (S.eKfam U a)) := by
    refine Pi.hom_ext _ _ (fun a => ?_)
    rw [Category.assoc]
    erw [Work.DSF1.Cech.cechComplexFunctor_map_pi U S.unitNat 0 a]
    rw [← Category.assoc]
    rw [show DSMap.coaug0 A X f U = Pi.lift (fun _ : (PerfSetup.CechIdx U 0).I =>
        DSMap.unitTop A X f ≫ (DSMap.cechPresheaf A X f).map (homOfLE le_top).op) from rfl]
    erw [Pi.lift_comp_π]
    rw [Category.assoc]
    rw [Category.assoc]
    erw [Pi.lift_comp_π]
    exact hC a
  have hνf : ν.f 0 = ((cechComplexFunctor U).map S.unitNat).f 0 ≫ lIso.inv.f 0 := by
    dsimp only [ν]
    rw [HomologicalComplex.comp_f]
  have hstep4 : DSMap.coaug0 A X f U ≫ ν.f 0 = DSMap.Mix2.unitA ψ ≫ R.map (S.eK U) := by
    rw [hνf]
    have hkey : (DSMap.coaug0 A X f U ≫
        (((cechComplexFunctor U).map S.unitNat).f 0 ≫ lIso.inv.f 0)) ≫
          piComparison R (S.Kobj U 0) =
        (DSMap.Mix2.unitA ψ ≫ R.map (S.eK U)) ≫ piComparison R (S.Kobj U 0) := by
      simp only [Category.assoc]
      rw [hpc, Category.comp_id, hmain, hEK]
    have h2 := congrArg (fun m => m ≫ inv (piComparison R (S.Kobj U 0))) hkey
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h2
  -- assemble
  refine ⟨φ ≫ μ, ?_⟩
  show ε ≫ ((φ ≫ μ).f 0 ≫
      R.map ((Kc.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom)) =
    DSMap.Mix2.unitA ψ ≫ R.map (S.eK U)
  calc ε ≫ ((φ ≫ μ).f 0 ≫ R.map ((Kc.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom))
      = ε ≫ (φ.f 0 ≫ (μ.f 0 ≫
          R.map ((Kc.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom))) := by
        rw [HomologicalComplex.comp_f]
        simp only [Category.assoc]
    _ = ε ≫ (φ.f 0 ≫ ((((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
            (i := 0) rfl).hom ≫ ν.f 0))) := by
        rw [hμ0']
    _ = (ε ≫ (φ.f 0 ≫ ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat
            (i := 0) rfl).hom)) ≫ ν.f 0 := by
        simp only [Category.assoc]
    _ = DSMap.coaug0 A X f U ≫ ν.f 0 := by
        rw [hφ]
    _ = DSMap.Mix2.unitA ψ ≫ R.map (S.eK U) := hstep4

end Work.DSEQP
