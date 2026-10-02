import Mathlib
import Submission.Work.Cohomology.relCohMV_honest_defs
import Submission.Work.Cohomology.relCohMV_honest_prereq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The quotient `C_*(X) ⟶ C_*(X,A)`, as a morphism with target `relChains X A`. -/
abbrev relChainsProj (X : TopCat) (A : Set X) : singularChains ℤ X ⟶ relChains X A :=
  cokernel.π (inclChains X A)

/-- The map of relative chain complexes induced by a map of pairs. -/
abbrev hmvPairsChains {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) : relChains X₁ A₁ ⟶ relChains X₂ A₂ :=
  relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h)

/-- Naturality of the quotient `C_*(X) ⟶ C_*(X,A)` with respect to a map of pairs. -/
lemma hmvRelDualProj_relChains {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relChainsProj X₁ A₁ ≫ hmvPairsChains A₁ A₂ f h
      = chainMap ℤ X₁ X₂ f ≫ relChainsProj X₂ A₂ := by
  rw [relChainsProj, hmvPairsChains, relChainsMapOf]
  refine cokernel_π_map (inclChains X₁ A₁) (inclChains X₂ A₂)
    (chainMap ℤ (TopCat.of A₁) (TopCat.of A₂) (relMapSub A₁ A₂ f h)) (chainMap ℤ X₁ X₂ f) ?_

/-! ## Restatements of the computation rules with target `relChains` -/

lemma hmv_mvPhi_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (smallInToSmall U V A) ≫ HMV.mvPhi X A U V
      = smallToSing U V ≫ relChainsProj X A :=
  HMV.mvPhi_comp X A U V

lemma hmv_etaU_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂U U V A) ≫ HMV.etaU A U V
      = smallInToSingA U V U ≫ relChainsProj (TopCat.of ↥U) (interAU A U) :=
  HMV.etaU_comp A U V

lemma hmv_etaV_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂V U V A) ≫ HMV.etaV A U V
      = smallInToSingA U V V ≫ relChainsProj (TopCat.of ↥V) (interAU A V) :=
  HMV.etaV_comp A U V

lemma hmv_relMVUVPhi_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₁ U V A) ≫ relMVUVPhi X A U V
      = SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)
        ≫ relChainsProj (topW X U V) (interAU A (U ∩ V)) := by
  have h : cokernel.π (relMVτ₁ U V A) ≫ relMVUVPhi X A U V
      = cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))
          ≫ relMVUVPhi X A U V := rfl
  rw [h, relMVUVPhi_comp, relChainsProj]
  congr 1

/-! ## Naturality of the duality isomorphism `relDualIsoComplex` -/

lemma dualChainMap_eq_dualComplexMap (X₁ X₂ : TopCat) (f : X₁ ⟶ X₂) :
    dualChainMap ℤ X₁ X₂ f
      = dualComplexMap ℤ (singularChains ℤ X₁) (singularChains ℤ X₂) (chainMap ℤ X₁ X₂ f) := rfl

/-- Compatibility of the relative cochain map of a pair with the inclusions. -/
lemma hmvRelComplexMap_comp_relIncl {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h ≫ relIncl ℤ X₁ A₁
      = relIncl ℤ X₂ A₂ ≫ dualChainMap ℤ X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relComplexMap_f, relIncl_f, relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact relMapLM_coe ℤ A₁ A₂ f h n x

/-- The duality isomorphism followed by the inclusion is the dual of the quotient map. -/
lemma hmvRelDualIsoComplex_hom_comp_relIncl (X : TopCat) (A : Set X) :
    (relDualIsoComplex X A).hom ≫ relIncl ℤ X A
      = dualComplexMap ℤ (singularChains ℤ X) (relChains X A)
          (cokernel.π (inclChains X A)) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relDualIsoComplex_hom_f, relIncl_f, dualComplexMap_f]
  exact relDualMap_comp_relIncl X A n

/-- The degreewise naturality of `relDualIso` with respect to a map of pairs. -/
lemma hmvRelDualIso_natural_f {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) :
    (relDualIso X₂ A₂ n).hom ≫ (relComplexMap ℤ A₁ A₂ f h).f n
      = dualComplexMapComp ℤ (relChains X₁ A₁) (relChains X₂ A₂)
          (hmvPairsChains A₁ A₂ f h) n ≫ (relDualIso X₁ A₁ n).hom := by
  haveI : Mono ((relIncl ℤ X₁ A₁).f n) := by
    rw [relIncl_f, ModuleCat.mono_iff_injective]
    intro a b hab
    exact Subtype.ext hab
  apply (cancel_mono ((relIncl ℤ X₁ A₁).f n)).1
  rw [Category.assoc, Category.assoc]
  have hdeg : (relComplexMap ℤ A₁ A₂ f h).f n ≫ (relIncl ℤ X₁ A₁).f n
      = (relIncl ℤ X₂ A₂).f n ≫ (dualChainMap ℤ X₁ X₂ f).f n := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      hmvRelComplexMap_comp_relIncl A₁ A₂ f h]
  rw [hdeg]
  rw [show (relDualIso X₁ A₁ n).hom ≫ (relIncl ℤ X₁ A₁).f n
      = dualComplexMapComp ℤ (singularChains ℤ X₁) (relChains X₁ A₁)
          (cokernel.π (inclChains X₁ A₁)) n from relDualMap_comp_relIncl X₁ A₁ n]
  rw [← Category.assoc]
  rw [show (relDualIso X₂ A₂ n).hom ≫ (relIncl ℤ X₂ A₂).f n
      = dualComplexMapComp ℤ (singularChains ℤ X₂) (relChains X₂ A₂)
          (cokernel.π (inclChains X₂ A₂)) n from relDualMap_comp_relIncl X₂ A₂ n]
  rw [show (dualChainMap ℤ X₁ X₂ f).f n
      = dualComplexMapComp ℤ (singularChains ℤ X₁) (singularChains ℤ X₂)
          (chainMap ℤ X₁ X₂ f) n from by
        rw [dualChainMap_eq_dualComplexMap, dualComplexMap_f]]
  rw [← dualComplexMapComp_comp, ← dualComplexMapComp_comp]
  rw [hmvRelDualProj_relChains (X₁ := X₁) (X₂ := X₂) A₁ A₂ f h]

/-- Naturality of the duality isomorphism `relDualIsoComplex` with respect to a map of pairs. -/
lemma hmvRelDualIsoComplex_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    (relDualIsoComplex X₂ A₂).hom ≫ relComplexMap ℤ A₁ A₂ f h
      = dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂) (hmvPairsChains A₁ A₂ f h)
          ≫ (relDualIsoComplex X₁ A₁).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relDualIsoComplex_hom_f,
    relDualIsoComplex_hom_f, dualComplexMap_f]
  exact hmvRelDualIso_natural_f A₁ A₂ f h n

/-- The mate of the naturality square. -/
lemma hmvRelComplexMap_comp_inv {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h ≫ (relDualIsoComplex X₁ A₁).inv
      = (relDualIsoComplex X₂ A₂).inv
          ≫ dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂) (hmvPairsChains A₁ A₂ f h) := by
  have hnat := hmvRelDualIsoComplex_natural A₁ A₂ f h
  calc relComplexMap ℤ A₁ A₂ f h ≫ (relDualIsoComplex X₁ A₁).inv
      = ((relDualIsoComplex X₂ A₂).inv ≫ (relDualIsoComplex X₂ A₂).hom)
          ≫ relComplexMap ℤ A₁ A₂ f h ≫ (relDualIsoComplex X₁ A₁).inv := by
          rw [Iso.inv_hom_id, Category.id_comp]
    _ = (relDualIsoComplex X₂ A₂).inv
          ≫ ((relDualIsoComplex X₂ A₂).hom ≫ relComplexMap ℤ A₁ A₂ f h)
          ≫ (relDualIsoComplex X₁ A₁).inv := by simp only [Category.assoc]
    _ = (relDualIsoComplex X₂ A₂).inv
          ≫ (dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂) (hmvPairsChains A₁ A₂ f h)
              ≫ (relDualIsoComplex X₁ A₁).hom)
          ≫ (relDualIsoComplex X₁ A₁).inv := by rw [hnat]
    _ = (relDualIsoComplex X₂ A₂).inv
          ≫ dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂) (hmvPairsChains A₁ A₂ f h) := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## The chain-level naturality squares -/

/-- Chain-level naturality of the `U`-component. -/
lemma hmvChain_natU (X : TopCat) (A U V : Set X) :
    HMV.alphaU X A U V ≫ HMV.mvPhi X A U V
      = HMV.etaU A U V ≫ hmvPairsChains (X₁ := TopCat.of ↥U) (X₂ := X) (interAU A U) A
          (subtypeIncl X U) (interAU_incl_subtypeIncl X A U) := by
  apply (cancel_epi (cokernel.π (relMVτ₂U U V A))).1
  rw [← Category.assoc, ← Category.assoc]
  rw [HMV.alphaU_comp X A U V, hmv_etaU_comp X A U V]
  rw [Category.assoc, Category.assoc]
  rw [hmv_mvPhi_comp X A U V]
  rw [hmvRelDualProj_relChains (X₁ := TopCat.of ↥U) (X₂ := X) (interAU A U) A
        (subtypeIncl X U) (interAU_incl_subtypeIncl X A U)]
  rw [← Category.assoc, ← Category.assoc]
  rw [← smallInToSingA_comp U V U]

/-- Chain-level naturality of the `V`-component. -/
lemma hmvChain_natV (X : TopCat) (A U V : Set X) :
    HMV.alphaV X A U V ≫ HMV.mvPhi X A U V
      = HMV.etaV A U V ≫ hmvPairsChains (X₁ := TopCat.of ↥V) (X₂ := X) (interAU A V) A
          (subtypeIncl X V) (interAU_incl_subtypeIncl_V X A V) := by
  apply (cancel_epi (cokernel.π (relMVτ₂V U V A))).1
  rw [← Category.assoc, ← Category.assoc]
  rw [HMV.alphaV_comp X A U V, hmv_etaV_comp X A U V]
  rw [Category.assoc, Category.assoc]
  rw [hmv_mvPhi_comp X A U V]
  rw [hmvRelDualProj_relChains (X₁ := TopCat.of ↥V) (X₂ := X) (interAU A V) A
        (subtypeIncl X V) (interAU_incl_subtypeIncl_V X A V)]
  rw [← Category.assoc, ← Category.assoc]
  rw [← smallInToSingA_comp U V V]

/-- Chain-level naturality of the overlap, `U`-component. -/
lemma hmvChain_natWU (X : TopCat) (A U V : Set X) :
    relMVUVPhi X A U V ≫ hmvPairsChains (X₁ := topW X U V) (X₂ := TopCat.of ↥U)
        (interAU A (U ∩ V)) (interAU A U)
        (pdIncl U (U ∩ V) Set.inter_subset_left) (interAU_incl_pdIncl_U X A U V)
      = HMV.gamma X A U V ≫ HMV.etaU A U V := by
  apply (cancel_epi (cokernel.π (relMVτ₁ U V A))).1
  rw [← Category.assoc, ← Category.assoc]
  rw [hmv_relMVUVPhi_comp X A U V, HMV.gamma_comp X A U V]
  rw [Category.assoc, Category.assoc]
  rw [hmvRelDualProj_relChains (X₁ := topW X U V) (X₂ := TopCat.of ↥U)
        (interAU A (U ∩ V)) (interAU A U)
        (pdIncl U (U ∩ V) Set.inter_subset_left) (interAU_incl_pdIncl_U X A U V)]
  rw [hmv_etaU_comp X A U V]
  rw [← Category.assoc, ← Category.assoc]
  rw [HMV.subInclChain_gen_natural' U V (Set.inter_subset_left : U ∩ V ⊆ U)]
  rfl

/-- Chain-level naturality of the overlap, `V`-component. -/
lemma hmvChain_natWV (X : TopCat) (A U V : Set X) :
    relMVUVPhi X A U V ≫ hmvPairsChains (X₁ := topW X U V) (X₂ := TopCat.of ↥V)
        (interAU A (U ∩ V)) (interAU A V)
        (pdIncl V (U ∩ V) Set.inter_subset_right) (interAU_incl_pdIncl_V X A U V)
      = HMV.delta X A U V ≫ HMV.etaV A U V := by
  apply (cancel_epi (cokernel.π (relMVτ₁ U V A))).1
  rw [← Category.assoc, ← Category.assoc]
  rw [hmv_relMVUVPhi_comp X A U V, HMV.delta_comp X A U V]
  rw [Category.assoc, Category.assoc]
  rw [hmvRelDualProj_relChains (X₁ := topW X U V) (X₂ := TopCat.of ↥V)
        (interAU A (U ∩ V)) (interAU A V)
        (pdIncl V (U ∩ V) Set.inter_subset_right) (interAU_incl_pdIncl_V X A U V)]
  rw [hmv_etaV_comp X A U V]
  rw [← Category.assoc, ← Category.assoc]
  rw [HMV.subInclChain_gen_natural' U V (Set.inter_subset_right : U ∩ V ⊆ V)]
  rfl

/-! ## The dualised naturality squares -/

lemma hmv_dualComp_natU (X : TopCat) (A U V : Set X) :
    dualComplexMap ℤ (relChains (TopCat.of ↥U) (interAU A U)) (relChains X A)
        (hmvPairsChains (X₁ := TopCat.of ↥U) (X₂ := X) (interAU A U) A
          (subtypeIncl X U) (interAU_incl_subtypeIncl X A U))
      ≫ dualComplexMap ℤ (relMVUU X A U V) (relChains (TopCat.of ↥U) (interAU A U))
          (HMV.etaU A U V)
    = dualComplexMap ℤ (relMVTopC X A U V) (relChains X A) (HMV.mvPhi X A U V)
      ≫ dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (HMV.alphaU X A U V) := by
  rw [← dualComplexMap_comp, ← dualComplexMap_comp, hmvChain_natU X A U V]

lemma hmv_dualComp_natV (X : TopCat) (A U V : Set X) :
    dualComplexMap ℤ (relChains (TopCat.of ↥V) (interAU A V)) (relChains X A)
        (hmvPairsChains (X₁ := TopCat.of ↥V) (X₂ := X) (interAU A V) A
          (subtypeIncl X V) (interAU_incl_subtypeIncl_V X A V))
      ≫ dualComplexMap ℤ (relMVVV X A U V) (relChains (TopCat.of ↥V) (interAU A V))
          (HMV.etaV A U V)
    = dualComplexMap ℤ (relMVTopC X A U V) (relChains X A) (HMV.mvPhi X A U V)
      ≫ dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (HMV.alphaV X A U V) := by
  rw [← dualComplexMap_comp, ← dualComplexMap_comp, hmvChain_natV X A U V]

lemma hmv_dualComp_natWU (X : TopCat) (A U V : Set X) :
    dualComplexMap ℤ (relChains (topW X U V) (interAU A (U ∩ V)))
        (relChains (TopCat.of ↥U) (interAU A U))
        (hmvPairsChains (X₁ := topW X U V) (X₂ := TopCat.of ↥U)
          (interAU A (U ∩ V)) (interAU A U)
          (pdIncl U (U ∩ V) Set.inter_subset_left) (interAU_incl_pdIncl_U X A U V))
      ≫ dualComplexMap ℤ (relMVUV X A U V) (relChains (topW X U V) (interAU A (U ∩ V)))
          (relMVUVPhi X A U V)
    = dualComplexMap ℤ (relMVUU X A U V) (relChains (TopCat.of ↥U) (interAU A U))
        (HMV.etaU A U V)
      ≫ dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V) := by
  rw [← dualComplexMap_comp, ← dualComplexMap_comp, hmvChain_natWU X A U V]

lemma hmv_dualComp_natWV (X : TopCat) (A U V : Set X) :
    dualComplexMap ℤ (relChains (topW X U V) (interAU A (U ∩ V)))
        (relChains (TopCat.of ↥V) (interAU A V))
        (hmvPairsChains (X₁ := topW X U V) (X₂ := TopCat.of ↥V)
          (interAU A (U ∩ V)) (interAU A V)
          (pdIncl V (U ∩ V) Set.inter_subset_right) (interAU_incl_pdIncl_V X A U V))
      ≫ dualComplexMap ℤ (relMVUV X A U V) (relChains (topW X U V) (interAU A (U ∩ V)))
          (relMVUVPhi X A U V)
    = dualComplexMap ℤ (relMVVV X A U V) (relChains (TopCat.of ↥V) (interAU A V))
        (HMV.etaV A U V)
      ≫ dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V) := by
  rw [← dualComplexMap_comp, ← dualComplexMap_comp, hmvChain_natWV X A U V]

/-! ## The four naturality identities -/

theorem hmv_naturality_U (X : TopCat) (A U V : Set X) :
    natU_lhs X A U V = natU_rhs X A U V := by
  unfold natU_lhs natU_rhs cmpU cmpX
  rw [← Category.assoc]
  rw [hmvRelComplexMap_comp_inv (X₁ := TopCat.of ↥U) (X₂ := X) (A₁ := interAU A U) (A₂ := A)
      (f := subtypeIncl X U) (h := interAU_incl_subtypeIncl X A U)]
  simp only [Category.assoc]
  rw [hmv_dualComp_natU X A U V]

theorem hmv_naturality_V (X : TopCat) (A U V : Set X) :
    natV_lhs X A U V = natV_rhs X A U V := by
  unfold natV_lhs natV_rhs cmpV cmpX
  rw [← Category.assoc]
  rw [hmvRelComplexMap_comp_inv (X₁ := TopCat.of ↥V) (X₂ := X) (A₁ := interAU A V) (A₂ := A)
      (f := subtypeIncl X V) (h := interAU_incl_subtypeIncl_V X A V)]
  simp only [Category.assoc]
  rw [hmv_dualComp_natV X A U V]

theorem hmv_naturality_WU (X : TopCat) (A U V : Set X) :
    natWU_lhs X A U V = natWU_rhs X A U V := by
  unfold natWU_lhs natWU_rhs cmpW cmpU
  rw [← Category.assoc]
  rw [hmvRelComplexMap_comp_inv (X₁ := topW X U V) (X₂ := TopCat.of ↥U)
      (A₁ := interAU A (U ∩ V)) (A₂ := interAU A U)
      (f := pdIncl U (U ∩ V) Set.inter_subset_left) (h := interAU_incl_pdIncl_U X A U V)]
  simp only [Category.assoc]
  rw [hmv_dualComp_natWU X A U V]

theorem hmv_naturality_WV (X : TopCat) (A U V : Set X) :
    natWV_lhs X A U V = natWV_rhs X A U V := by
  unfold natWV_lhs natWV_rhs cmpW cmpV
  rw [← Category.assoc]
  rw [hmvRelComplexMap_comp_inv (X₁ := topW X U V) (X₂ := TopCat.of ↥V)
      (A₁ := interAU A (U ∩ V)) (A₂ := interAU A V)
      (f := pdIncl V (U ∩ V) Set.inter_subset_right) (h := interAU_incl_pdIncl_V X A U V)]
  simp only [Category.assoc]
  rw [hmv_dualComp_natWV X A U V]

/-- **Naturality of the comparison maps of the relative Mayer–Vietoris sequence.** -/
theorem hmv_naturality (X : TopCat) (A U V : Set X) :
    (Work.Cohomology.natU_lhs X A U V = Work.Cohomology.natU_rhs X A U V) ∧
    (Work.Cohomology.natV_lhs X A U V = Work.Cohomology.natV_rhs X A U V) ∧
    (Work.Cohomology.natWU_lhs X A U V = Work.Cohomology.natWU_rhs X A U V) ∧
    (Work.Cohomology.natWV_lhs X A U V = Work.Cohomology.natWV_rhs X A U V) :=
  ⟨hmv_naturality_U X A U V, hmv_naturality_V X A U V, hmv_naturality_WU X A U V,
    hmv_naturality_WV X A U V⟩

end

end Work.Cohomology
