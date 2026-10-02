import Mathlib
import Submission.Work.Thom.cupDeltaInfra
import Submission.Work.Thom.transgressionFleetDefs
import Submission.Work.Thom.cup_hmvF
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.relCochainDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

set_option allowUnsafeReducibility true

attribute [local implicit_reducible] HomologicalComplex.restriction
attribute [local implicit_reducible] TopCat.toSSet
attribute [local implicit_reducible] Work.Cohomology.relKern
attribute [local implicit_reducible] Work.Cohomology.smallInSubcomplex
attribute [local implicit_reducible] Work.Cohomology.smallSubcomplex
attribute [local implicit_reducible] Work.Cohomology.dualComplex
attribute [local implicit_reducible] CochainComplex.of
attribute [local implicit_reducible] Work.Cohomology.dualObj

namespace Work.Thom

lemma dualComplexMapComp_hom_apply_local {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ)
    (ω : (D.X n) →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n) ω
      = LinearMap.dualMap (ModuleCat.Hom.hom (f.f n)) ω := rfl

lemma dualComplexMapComp_hom_eq_local {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ) :
    ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n)
      = LinearMap.dualMap (ModuleCat.Hom.hom (f.f n)) :=
  LinearMap.ext (fun ω => dualComplexMapComp_hom_apply_local f n ω)

lemma epi_cokernelπ_f_local {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    Epi ((cokernel.π f).f n) := by
  have hfac : (cokernel.π f).f n = cokernel.π (f.f n) ≫ (cokernelComponentIso f n).inv := by
    rw [← cokernelComponentIso_canon f n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac]; infer_instance

lemma mono_dualComplexMapComp_of_epi_local {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ)
    (hf : Epi (f.f n)) : Mono (dualComplexMapComp ℤ C D f n) := by
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective ⇑(ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n))
  rw [dualComplexMapComp_hom_eq_local]
  exact LinearMap.dualMap_injective_of_surjective ((ModuleCat.epi_iff_surjective _).mp hf)

end Work.Thom

namespace Work.Thom

lemma relDualIsoComplex_hom_comp_relIncl_local (X : TopCat) (A : Set X) :
    (relDualIsoComplex X A).hom ≫ relIncl ℤ X A
      = dualComplexMap ℤ (singularChains ℤ X) (relChains X A) (cokernel.π (inclChains X A)) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relDualIsoComplex_hom_f, relDualIso_hom, dualComplexMap_f]
  exact relDualMap_comp_relIncl X A n

end Work.Thom

namespace Work.Thom

lemma cmpX_comp_proj_local (X : TopCat) (A U V : Set X) :
    cmpX X A U V ≫ dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))
      = relIncl ℤ X A
          ≫ dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V) := by
  rw [cmpX, Category.assoc]
  rw [← dualComplexMap_comp ℤ (cokernel.π (smallInToSmall U V A)) (HMV.mvPhi X A U V)]
  rw [HMV.mvPhi_comp]
  rw [dualComplexMap_comp (C := smallChains U V) (D := singularChains ℤ X)
      (E := relChains X A) ℤ (smallToSing U V) (cokernel.π (inclChains X A))]
  rw [← Category.assoc, ← relDualIsoComplex_hom_comp_relIncl_local X A]
  rw [Iso.inv_hom_id_assoc]

end Work.Thom

namespace Work.Thom

lemma cmpX_proj_f_local (X : TopCat) (A U V : Set X) (m : ℕ)
    (φ : ↥((relComplex ℤ X A).X m)) :
    (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))).f m ((cmpX X A U V).f m φ)
      = (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)).f m
          ((relIncl ℤ X A).f m φ) := by
  have h := congrArg (fun (g : relComplex ℤ X A ⟶ dualComplex ℤ (smallChains U V)) =>
      ModuleCat.Hom.hom (g.f m) φ) (cmpX_comp_proj_local X A U V)
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

lemma relIncl_apply_local (X : TopCat) (A : Set X) (m : ℕ)
    (φ : ↥((relComplex ℤ X A).X m)) :
    (relIncl ℤ X A).f m φ = φ.1 := rfl

lemma dualComplexMap_apply_comp_local {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (m : ℕ)
    (ω : ↥(dualObj ℤ D m)) :
    (dualComplexMap ℤ C D f).f m ω = ω.comp ((f.f m).hom) := by
  rw [dualComplexMap_f]
  exact dualComplexMapComp_apply' ℤ C D f m ω

lemma cup_smallToSing_local (X : TopCat) (U V : Set X) (n j : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) j) (β : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (cup ℤ (TopCat.toSSet.obj X) α β).comp ((smallToSing U V).f (j + n)).hom
      = cup ℤ (smallSSet U V) (α.comp ((smallToSing U V).f j).hom) (restrSmall X U V n β) := by
  have h := cupHom_chainComplexMap (g := (smallSubcomplex U V).ι) (α := α) (β := β)
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp] at h2
  exact h2

end Work.Thom

namespace Work.Thom

lemma cupSmallCochain_apply_local (X : TopCat) (U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n)
    (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    cupSmallCochain X U V n p t ψ = cup ℤ (smallSSet U V) ψ (restrSmall X U V n t) := rfl

theorem cupCmpRestrictTop (X : TopCat) (A U V : Set X) (n j : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (c : ↥((Work.Cohomology.relComplex ℤ X ∅).X j)) :
    (Work.Cohomology.cmpX X A U V).f (j + n) ((Work.Thom.cupRightLM t ∅ j) c)
      = Work.Thom.cupTop X A U V n j t.1 t.2 ((Work.Cohomology.cmpX X ∅ U V).f j c) := by
  have hL : (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))).f (j + n)
        ((cmpX X A U V).f (j + n) ((cupRightLM t ∅ j) c))
      = (cup ℤ (TopCat.toSSet.obj X) c.1 t.1).comp ((smallToSing U V).f (j + n)).hom := by
    rw [cmpX_proj_f_local X A U V (j + n) (cupRightLM t ∅ j c)]
    rw [relIncl_apply_local, cupRightLM_apply, dualComplexMap_apply_comp_local]
  have hψ : (dualComplexMap ℤ (smallChains U V) (relMVTopC X ∅ U V)
        (cokernel.π (smallInToSmall U V ∅))).f j ((cmpX X ∅ U V).f j c)
      = c.1.comp ((smallToSing U V).f j).hom := by
    rw [cmpX_proj_f_local X ∅ U V j c, relIncl_apply_local, dualComplexMap_apply_comp_local]
  have hR : (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))).f (j + n)
        (cupTop X A U V n j t.1 t.2 ((cmpX X ∅ U V).f j c))
      = cup ℤ (smallSSet U V) (c.1.comp ((smallToSing U V).f j).hom)
          (restrSmall X U V n t.1) := by
    rw [cupTop_eq, ConcreteCategory.comp_apply, hψ]
    rw [← cupSmallCochain_apply_local, ← cupTopDesc_comp X A U V n j t.1 t.2]
    rw [ConcreteCategory.comp_apply]
  have hmain : (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))).f (j + n)
        ((cmpX X A U V).f (j + n) ((cupRightLM t ∅ j) c))
      = (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))).f (j + n)
        (cupTop X A U V n j t.1 t.2 ((cmpX X ∅ U V).f j c)) := by
    rw [hL, hR]
    exact cup_smallToSing_local X U V n j c.1 t.1
  haveI hm : Mono ((dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
        (cokernel.π (smallInToSmall U V A))).f (j + n)) := by
    rw [dualComplexMap_f]
    exact mono_dualComplexMapComp_of_epi_local _ _ (epi_cokernelπ_f_local _ _)
  exact (ModuleCat.mono_iff_injective _).mp hm hmain


end Work.Thom
