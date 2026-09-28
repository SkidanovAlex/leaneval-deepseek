import Mathlib
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.localHomology

/-!
# The pair map on relative cochains is the dual of the pair map on relative chains (compatible world)

The relative cochain complex `C^*(X,A;ℤ)` is `ℤ`-dual to the relative chain complex
`C_*(X,A;ℤ)` (`Work.Cohomology.relCochainDual`), and this identification is natural in a map of
pairs.  Consequently a map of pairs `(X₁,A₁) → (X₂,A₂)` whose two components are homology
isomorphisms induces an isomorphism on relative cohomology — the homotopy invariance of the
relative cohomology of a pair.

The analogous statement in the world of `dualZ` (`Submission/Work/Cohomology/Crux/
relComplexMap_homologyMap_isIso.lean`) is NOT importable here: this module and its whole import
closure must avoid `Submission.Work.Cohomology.dualZ` and
`Submission.Work.Cohomology.prodSphereAux`.  The proof below redoes the duality naturality in the
compatible language of `dualComplex` / `relDualEquiv`.

## Main results

* `relDualProj_relChainsMapOf_compat` — the quotient map `C_*(X) ⟶ C_*(X,A)` is natural;
* `relDualEquiv_natural` — the degreewise duality isomorphism is natural for a map of pairs;
* `relCochainDualIso` — the duality isomorphism of complexes, with computable components;
* `relComplexMapHomologyIsoCompat` — a map of pairs whose components are quasi-isomorphisms induces
  an isomorphism on relative cohomology.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology.Crux

noncomputable section

/-- The map of relative chain complexes induced by a map of pairs, in normal form. -/
abbrev relPairsChainsMapCompat {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) : relChains X₁ A₁ ⟶ relChains X₂ A₂ :=
  relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h)

/-- **Naturality of the quotient map `C_*(X) ⟶ C_*(X,A)` with respect to a map of pairs.** -/
theorem relDualProj_relChainsMapOf_compat {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (g : TopCat.of A₁ ⟶ TopCat.of A₂)
    (w : subtypeIncl X₁ A₁ ≫ f = g ≫ subtypeIncl X₂ A₂) (n : ℕ) :
    relDualProj X₁ A₁ n ≫ (relChainsMapOf X₁ X₂ A₁ A₂ f g w).f n
      = (chainMap ℤ X₁ X₂ f).f n ≫ relDualProj X₂ A₂ n := by
  have hw : inclChains X₁ A₁ ≫ chainMap ℤ X₁ X₂ f
      = chainMap ℤ (TopCat.of A₁) (TopCat.of A₂) g ≫ inclChains X₂ A₂ := by
    simp only [inclChains, chainMap, ← Functor.map_comp, w]
  have h := cokernel_π_map (inclChains X₁ A₁) (inclChains X₂ A₂)
    (chainMap ℤ (TopCat.of A₁) (TopCat.of A₂) g) (chainMap ℤ X₁ X₂ f) hw
  have h2 := congrArg (fun k => k.f n) h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h2
  rw [relChainsMapOf]
  exact h2

/-- **The transpose of the chain map `chainMap f`, evaluated on a cochain and a chain.** -/
theorem relDualLM_dualChainMap_apply (X₁ X₂ : TopCat) (f : X₁ ⟶ X₂) (n : ℕ)
    (y : ↥((singularCochainComplex ℤ X₂).X n)) (x : ↥((singularChains ℤ X₁).X n)) :
    relDualLM X₁ n (((dualChainMap ℤ X₁ X₂ f).f n).hom y) x
      = relDualLM X₂ n y (((chainMap ℤ X₁ X₂ f).f n).hom x) := by
  rw [show ModuleCat.Hom.hom ((dualChainMap ℤ X₁ X₂ f).f n)
      = (ModuleCat.Hom.hom ((chainMap ℤ X₁ X₂ f).f n)).dualMap
      from dualChainMap_f_hom ℤ X₁ X₂ f n]
  exact LinearMap.dualMap_apply _ _ x

/-- **Naturality of the degreewise duality isomorphism**, evaluated at a chain. -/
theorem relDualMap_natural_app {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (ψ : ↥((relChains X₂ A₂).X n) →ₗ[ℤ] ℤ)
    (x : ↥((singularChains ℤ X₁).X n)) :
    relDualLM X₁ n (relDualMap X₁ A₁ n ((dualComplexMapComp ℤ (relChains X₁ A₁)
        (relChains X₂ A₂) (relPairsChainsMapCompat A₁ A₂ f h) n).hom ψ)).1 x
      = relDualLM X₁ n (relMapLM ℤ A₁ A₂ f h n (relDualMap X₂ A₂ n ψ)).1 x := by
  have hL : relDualLM X₁ n (relDualMap X₁ A₁ n ((dualComplexMapComp ℤ (relChains X₁ A₁)
        (relChains X₂ A₂) (relPairsChainsMapCompat A₁ A₂ f h) n).hom ψ)).1 x
      = ψ ((ModuleCat.Hom.hom ((relPairsChainsMapCompat A₁ A₂ f h).f n))
            ((ModuleCat.Hom.hom (relDualProj X₁ A₁ n)) x)) := by
    rw [relDualMap_apply]
    exact dualComplexMapComp_apply ℤ (relChains X₁ A₁) (relChains X₂ A₂)
      (relPairsChainsMapCompat A₁ A₂ f h) n ψ ((relDualProj X₁ A₁ n) x)
  have hR : relDualLM X₁ n (relMapLM ℤ A₁ A₂ f h n (relDualMap X₂ A₂ n ψ)).1 x
      = ψ ((ModuleCat.Hom.hom (relDualProj X₂ A₂ n))
            ((ModuleCat.Hom.hom ((chainMap ℤ X₁ X₂ f).f n)) x)) :=
    calc relDualLM X₁ n (relMapLM ℤ A₁ A₂ f h n (relDualMap X₂ A₂ n ψ)).1 x
        = relDualLM X₁ n (((dualChainMap ℤ X₁ X₂ f).f n).hom
            (relDualMap X₂ A₂ n ψ).1) x :=
          congrArg (fun (g : ↥((singularCochainComplex ℤ X₁).X n)) => relDualLM X₁ n g x)
            (relMapLM_coe ℤ A₁ A₂ f h n (relDualMap X₂ A₂ n ψ))
      _ = relDualLM X₂ n (relDualMap X₂ A₂ n ψ).1
            (((chainMap ℤ X₁ X₂ f).f n).hom x) :=
          relDualLM_dualChainMap_apply X₁ X₂ f n (relDualMap X₂ A₂ n ψ).1 x
      _ = ψ ((ModuleCat.Hom.hom (relDualProj X₂ A₂ n))
            ((ModuleCat.Hom.hom ((chainMap ℤ X₁ X₂ f).f n)) x)) :=
          relDualMap_apply X₂ A₂ n ψ (((chainMap ℤ X₁ X₂ f).f n).hom x)
  rw [hL, hR]
  refine congrArg ψ ?_
  have hnat := congrArg (fun (k : (singularChains ℤ X₁).X n ⟶ (relChains X₂ A₂).X n) =>
      (ModuleCat.Hom.hom k) x)
    (relDualProj_relChainsMapOf_compat A₁ A₂ f (relMapSub A₁ A₂ f h)
      (relMapSub_spec A₁ A₂ f h) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hnat

/-- **Naturality of the degreewise duality isomorphism `relDualMap`** for a map of pairs. -/
theorem relDualMap_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (ψ : ↥((relChains X₂ A₂).X n) →ₗ[ℤ] ℤ) :
    relDualMap X₁ A₁ n ((dualComplexMapComp ℤ (relChains X₁ A₁) (relChains X₂ A₂)
        (relPairsChainsMapCompat A₁ A₂ f h) n).hom ψ)
      = relMapLM ℤ A₁ A₂ f h n (relDualMap X₂ A₂ n ψ) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact relDualMap_natural_app A₁ A₂ f h n ψ x

/-- **Naturality of the degreewise duality isomorphism `relDualEquiv`** for a map of pairs. -/
theorem relDualEquiv_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (ψ : ↥((relChains X₂ A₂).X n) →ₗ[ℤ] ℤ) :
    relDualEquiv X₁ A₁ n ((dualComplexMapComp ℤ (relChains X₁ A₁) (relChains X₂ A₂)
        (relPairsChainsMapCompat A₁ A₂ f h) n).hom ψ)
      = relMapLM ℤ A₁ A₂ f h n (relDualEquiv X₂ A₂ n ψ) := by
  rw [relDualEquiv_apply, relDualEquiv_apply]
  exact relDualMap_natural A₁ A₂ f h n ψ

/-- **The duality isomorphism of cochain complexes**, with computable components: the `n`-th
component is `relDualIso X A n = relDualMap X A n`. -/
noncomputable def relCochainDualIso (X : TopCat) (A : Set X) :
    dualComplex ℤ (relChains X A) ≅ relComplex ℤ X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => relDualIso X A n) (fun i j hij => by
    rw [← hij]
    exact relDualIso_comm X A i)

@[simp] theorem relCochainDualIso_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relCochainDualIso X A).hom.f n = (relDualIso X A n).hom :=
  HomologicalComplex.Hom.isoOfComponents_hom_f _ _ n

@[simp] theorem relCochainDualIso_inv_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relCochainDualIso X A).inv.f n = (relDualIso X A n).inv :=
  HomologicalComplex.Hom.isoOfComponents_inv_f _ _ n

/-- The inverse of the degreewise duality isomorphism is the inverse linear equivalence. -/
theorem relDualIso_inv_apply (X : TopCat) (A : Set X) (n : ℕ) :
    (relDualIso X A n).inv = ModuleCat.ofHom ((relDualEquiv X A n).symm).toLinearMap := by
  rw [relDualIso, LinearEquiv.toModuleIso_inv]

/-- **The pair map on relative cochains is the duality conjugate of the pair map on relative
chains.** -/
theorem relComplexMap_dual (X₁ X₂ : TopCat) (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h
      = (relCochainDualIso X₂ A₂).inv
        ≫ dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂) (relPairsChainsMapCompat A₁ A₂ f h)
        ≫ (relCochainDualIso X₁ A₁).hom := by
  apply HomologicalComplex.hom_ext
  intro m
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relCochainDualIso_inv_f,
    relCochainDualIso_hom_f, relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show (relMapLM ℤ A₁ A₂ f h m) x
      = (relDualMap X₁ A₁ m) ((dualComplexMapComp ℤ (relChains X₁ A₁) (relChains X₂ A₂)
          (relPairsChainsMapCompat A₁ A₂ f h) m).hom ((relDualEquiv X₂ A₂ m).symm x))
  rw [← show relMapLM ℤ A₁ A₂ f h m (relDualMap X₂ A₂ m ((relDualEquiv X₂ A₂ m).symm x))
      = relMapLM ℤ A₁ A₂ f h m x from by
        rw [← relDualEquiv_apply, LinearEquiv.apply_symm_apply]]
  exact (relDualMap_natural A₁ A₂ f h m ((relDualEquiv X₂ A₂ m).symm x)).symm

/-- **A map of pairs whose two components are homology isomorphisms induces an isomorphism on
relative cohomology.** -/
theorem relComplexMapHomologyIsoCompat {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ)
    (hf : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (chainMap ℤ X₁ X₂ f) k))
    (hg : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A₁) (TopCat.of A₂) (relMapSub A₁ A₂ f h)) k)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ A₁ A₂ f h) n) := by
  have hφ : ∀ k, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relPairsChainsMapCompat A₁ A₂ f h) k) := fun k =>
    relChainsMapOf_isIso A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h) k hf hg
  have hdual : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂)
        (relPairsChainsMapCompat A₁ A₂ f h)) n) :=
    dualComplexMap_quasiIso (relPairsChainsMapCompat A₁ A₂ f h)
      (fun k => relChainsProjective X₁ A₁ k) (fun k => relChainsProjective X₂ A₂ k) hφ n
  rw [relComplexMap_dual X₁ X₂ A₁ A₂ f h, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  haveI := hdual
  infer_instance

end

end Work.Cohomology.Crux
