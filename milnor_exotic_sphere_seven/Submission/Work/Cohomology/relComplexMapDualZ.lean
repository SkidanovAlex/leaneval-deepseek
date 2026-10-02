import Mathlib
import Submission.Work.Cohomology.cappedPairDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pair map on relative cochains is the `ℤ`-dual of the pair map on relative chains

The relative cochain complex `C^*(X,A;R)` is `relZIso`-naturally the `ℤ`-dual of the relative chain
complex `C_*(X,A;ℤ)` (`Submission/Work/Cohomology/relComplexIsoDualZ.lean`).  This file proves that
this identification is **natural** with respect to a map of pairs: for a continuous map
`f : X₁ ⟶ X₂` with `f '' A₁ ⊆ A₂`, the induced map of relative cochain complexes is the conjugate of
the transposed induced map of relative chain complexes under `relZIso`.

The proof is degreewise.  After establishing

* the naturality of the quotient map `relDualProj` with respect to `relChainsMapOf`
  (`relDualProj_relChainsMapOf`), and
* the compatibility of the coefficient comparison `cochCoeffEquiv` with the pullback of a
  continuous map (`dualChainMap_cochCoeffEquiv`),

the key statement is the naturality of the degreewise isomorphism `relZEquiv`
(`relZEquiv_natural`), from which the identity of cochain maps follows by extensionality.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The map of relative chain complexes induced by a map of pairs, in the normal form used
throughout this file. -/
abbrev relPairsChainsMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) : relChains X₁ A₁ ⟶ relChains X₂ A₂ :=
  relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h)

/-- **The coefficient comparison is compatible with the pullback of a continuous map**: pulling a
functional on the `ℤ`-chains of `Y` back along `f : X ⟶ Y` (as a functional on the `R`-chains of
`X`) corresponds under `cochCoeffEquiv` to precomposing with the induced map of `ℤ`-chains. -/
lemma dualChainMap_cochCoeffEquiv {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (Θ : (singularChains ℤ Y).X n →ₗ[ℤ] R) :
    (cochainPullbackHom R X Y f n).hom (cochCoeffEquiv R Y n Θ)
      = cochCoeffEquiv R X n (Θ.comp ((chainMap ℤ X Y f).f n).hom) := by
  apply LinearMap.ext; intro x
  rw [cochainPullbackHom_apply, cochCoeffEquiv_natural R f n Θ, LinearMap.comp_apply]

/-- **Naturality of the quotient map `C_*(X) ⟶ C_*(X,A)` with respect to a map of pairs.** -/
lemma relDualProj_relChainsMapOf {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (g : TopCat.of A₁ ⟶ TopCat.of A₂)
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

/-- **Naturality of the degreewise duality isomorphism `relZEquiv`.**  The identification of the
`n`-th relative cochains with the `ℤ`-dual of the relative `n`-chains is compatible with the
contravariant map induced by a map of pairs. -/
lemma relZEquiv_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) (ψ : (relChains X₂ A₂).X n →ₗ[ℤ] R) :
    relZEquiv R X₁ A₁ n
        ((dualZMapComp R (relChains X₁ A₁) (relChains X₂ A₂)
          (relPairsChainsMap A₁ A₂ f h) n).hom ψ)
      = relMapLM R A₁ A₂ f h n (relZEquiv R X₂ A₂ n ψ) := by
  apply Subtype.ext
  change (cochCoeffEquiv R X₁ n ((dualZMapComp R (relChains X₁ A₁) (relChains X₂ A₂)
          (relPairsChainsMap A₁ A₂ f h) n).hom ψ |>.comp (relDualProj X₁ A₁ n).hom)
        : (singularChains R X₁).X n →ₗ[R] R)
      = ((cochainPullbackHom R X₁ X₂ f n).hom
          (cochCoeffEquiv R X₂ n (ψ.comp (relDualProj X₂ A₂ n).hom))
        : (singularChains R X₁).X n →ₗ[R] R)
  rw [dualChainMap_cochCoeffEquiv R f n (ψ.comp (relDualProj X₂ A₂ n).hom)]
  rw [dualZMapComp_apply']
  apply congrArg
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
  apply congrArg
  have hnat := congrArg (fun k => ModuleCat.Hom.hom k)
    (relDualProj_relChainsMapOf A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hnat
  exact hnat

/-- **The degreewise form of the compatibility of `relZIso` with the pair map.** -/
lemma relZIso_comp_relComplexMap_f {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) :
    (relZIso R X₂ A₂ n).hom ≫ (relComplexMap R A₁ A₂ f h).f n
      = (dualZMapComp R (relChains X₁ A₁) (relChains X₂ A₂)
          (relPairsChainsMap A₁ A₂ f h) n) ≫ (relZIso R X₁ A₁ n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [relComplexMap_f, relZIso_hom, dualZ_X]
  exact (relZEquiv_natural R A₁ A₂ f h n ψ).symm

theorem relComplexMapDualZ (R : Type) [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    Work.Cohomology.relComplexMap R A₁ A₂ f h
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.Iso.inv (Work.Cohomology.relZIsoComplex R X₂ A₂))
            (Work.Cohomology.dualZMap R (Work.Cohomology.relChains X₁ A₁)
              (Work.Cohomology.relChains X₂ A₂)
              (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ f
                (Work.Cohomology.relMapSub A₁ A₂ f h)
                (Work.Cohomology.relMapSub_spec A₁ A₂ f h))))
          (CategoryTheory.Iso.hom (Work.Cohomology.relZIsoComplex R X₁ A₁)) := by
  have h' : (relZIsoComplex R X₂ A₂).hom ≫ relComplexMap R A₁ A₂ f h
      = dualZMap R (relChains X₁ A₁) (relChains X₂ A₂) (relPairsChainsMap A₁ A₂ f h)
          ≫ (relZIsoComplex R X₁ A₁).hom := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relZIsoComplex_hom_f,
      relZIsoComplex_hom_f, dualZMap_f]
    exact relZIso_comp_relComplexMap_f R A₁ A₂ f h n
  rw [Category.assoc, ← h', Iso.inv_hom_id_assoc]

end

end Work.Cohomology
