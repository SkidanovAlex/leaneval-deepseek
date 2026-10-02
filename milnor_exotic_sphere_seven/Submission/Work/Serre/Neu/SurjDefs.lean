-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/Defs.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.StemsB.WangCohRat
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Serre.crossProduct_defs
import Submission.Work.Kunneth.Chapter
import Submission.Work.Serre.Surj.DZGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## The base change on components -/

/-- The component of the base change of a chain map on a pure tensor. -/
theorem IntRatCM_map_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (x : ↥(C.X n)) :
    (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map f).f n)) (TensorProduct.tmul ℤ (1 : ℚ) x)
      = TensorProduct.tmul ℤ (1 : ℚ) ((f.f n).hom x) := by
  simp only [Work.StemsB.IntRatCM, Functor.mapHomologicalComplex_map_f]
  exact ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) (f.f n) (1 : ℚ) x

/-- The differential of the base change of a chain complex on a pure tensor. -/
theorem IntRatCM_d_tmul (C : ChainComplex (ModuleCat ℤ) ℕ) (i j : ℕ) (x : ↥(C.X i)) :
    (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj C).d i j)) (TensorProduct.tmul ℤ (1 : ℚ) x)
      = TensorProduct.tmul ℤ (1 : ℚ) ((C.d i j).hom x) := by
  simp only [Work.StemsB.IntRatCM, Functor.mapHomologicalComplex_obj_d]
  exact ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) (C.d i j) (1 : ℚ) x

/-! ## The base change isomorphisms of the (relative) chain complexes -/

/-- The base change `C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)` of the absolute singular chains. -/
abbrev bcAbs (X : Type) [TopologicalSpace X] :
    Work.StemsB.IntRatCM.obj (Work.Cohomology.singularChains ℤ (TopCat.of X)) ≅
      Work.Cohomology.singularChains ℚ (TopCat.of X) :=
  Work.StemsB.RatBC.Phi (Work.Serre.singSSetN X)

/-- The quotient chain map `C_*(X;R) ⟶ C_*(X,A;R)`, as a morphism of chain complexes. -/
abbrev relChainsProjR (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    Work.Cohomology.singularChains R X ⟶ Work.StemsB.relChainsR R X A :=
  cokernel.π (Work.StemsB.relChainsRIncl R X A)

/-- **Base change of the relative singular chains.**  The explicit form of
`Work.StemsB.relChainsBaseChangeRat` (the `Nonempty` there is replaced by the chosen iso), so that
its naturality can be used. -/
noncomputable def bcRel (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains X A) ≅ Work.StemsB.relChainsR ℚ X A := by
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  have : PreservesFiniteColimits Work.StemsB.IntRatCM := inferInstance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatCM := inferInstance
  have hsq : Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A)
      ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom
      = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom
      ≫ Work.StemsB.relChainsRIncl ℚ X A :=
    (Work.StemsB.RatBC.Phi_naturality
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))).symm
  exact Limits.PreservesCokernel.iso Work.StemsB.IntRatCM (Work.Cohomology.inclChains X A) ≪≫
    Limits.cokernel.mapIso (Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
      (Work.StemsB.relChainsRIncl ℚ X A)
      (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A)))
      (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)) hsq

/-- **Naturality of `bcRel` with respect to the quotient map** `C_*(X;R) ⟶ C_*(X,A;R)`. -/
theorem bcRel_naturality (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsProj X A) ≫ (bcRel X A).hom
      = (bcAbs ↥X).hom ≫ relChainsProjR ℚ X A := by
  haveI : PreservesFiniteColimits Work.StemsB.IntRatCM := inferInstance
  have hdef : (bcRel X A).hom
      = (Limits.PreservesCokernel.iso Work.StemsB.IntRatCM (Work.Cohomology.inclChains X A)).hom
        ≫ (Limits.cokernel.mapIso (f := Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
            (f' := Work.StemsB.relChainsRIncl ℚ X A)
            (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A)))
            (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X))
            (Work.StemsB.RatBC.Phi_naturality
              (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))).symm).hom := rfl
  rw [hdef, ← Category.assoc, Limits.PreservesCokernel.π_iso_hom]
  dsimp only [Limits.cokernel.mapIso]
  exact cokernel.π_desc (f := Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A)) _ _

/-- The value of `bcRel` on the quotient of a pure tensor: the naturality square of
`bcRel_naturality` in the form used in the assembly. -/
theorem bcRel_value (X : TopCat) (A : Set X) (n : ℕ)
    (y : ↥((Work.Cohomology.singularChains ℤ X).X n)) :
    (ModuleCat.Hom.hom ((bcRel X A).hom.f n))
        (TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj X A).f n)) y))
      = (ModuleCat.Hom.hom ((relChainsProjR ℚ X A).f n))
          (ModuleCat.Hom.hom ((bcAbs ↥X).hom.f n) (TensorProduct.tmul ℤ (1 : ℚ) y)) := by
  have h1 : (ModuleCat.Hom.hom ((bcRel X A).hom.f n)).comp
        (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsProj X A)).f n))
      = (ModuleCat.Hom.hom ((relChainsProjR ℚ X A).f n)).comp
        (ModuleCat.Hom.hom ((bcAbs ↥X).hom.f n)) := by
    have h := congrArg (fun (g : Work.StemsB.IntRatCM.obj (Work.Cohomology.singularChains ℤ X) ⟶
        Work.StemsB.relChainsR ℚ X A) => ModuleCat.Hom.hom (g.f n)) (bcRel_naturality X A)
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp] using h
  rw [show TensorProduct.tmul ℤ (1 : ℚ)
        ((ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj X A).f n)) y)
      = (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.map
          (Work.Cohomology.relChainsProj X A)).f n)) (TensorProduct.tmul ℤ (1 : ℚ) y)
      from (IntRatCM_map_tmul _ _ _ _ _).symm]
  rw [← LinearMap.comp_apply, h1, LinearMap.comp_apply]

/-! ## The value of the homology map on classes of cycles -/

/-- The value of `homologyMap` on the class of a cycle. -/
theorem homologyMap_homologyπ (K L : ChainComplex (ModuleCat ℤ) ℕ) (f : K ⟶ L) (n : ℕ)
    (x : ↥(K.cycles n)) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap f n)) ((ModuleCat.Hom.hom (K.homologyπ n)) x)
      = (ModuleCat.Hom.hom (L.homologyπ n)) ((HomologicalComplex.cyclesMap f n) x) := by
  have h := congrArg (fun (g : K.cycles n ⟶ L.homology n) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.homologyπ_naturality (φ := f) (i := n))
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The underlying chain of the image of a cycle under `cyclesMap`, in `iCycles` form. -/
theorem iCycles_cyclesMap (K L : ChainComplex (ModuleCat ℤ) ℕ) (f : K ⟶ L) (n : ℕ)
    (x : ↥(K.cycles n)) :
    (ModuleCat.Hom.hom (L.iCycles n)) ((HomologicalComplex.cyclesMap f n) x)
      = (ModuleCat.Hom.hom (f.f n)) ((ModuleCat.Hom.hom (K.iCycles n)) x) := by
  have h := congrArg (fun (g : K.cycles n ⟶ L.X n) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.cyclesMap_i (φ := f) (i := n))
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

end

end Work.Serre.Surj
