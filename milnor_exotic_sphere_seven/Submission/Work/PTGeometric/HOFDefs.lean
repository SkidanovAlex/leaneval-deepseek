import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.excision
import Submission.Work.Tubular.convexLocalIso_free
import Submission.Work.Tubular.exists_halfOrientationFamily_euclidean
import Submission.Work.ThomBordism.doubleFC.relFactor
import Submission.Work.RatHurewicz.relHurewiczClass_eq_of_homotopic
import Submission.Work.RatHurewicz.Cofibre.homologyMap_uMap_comp_relPairMap
import Submission.Work.Thom.PairPrism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local-homology framework for `exists_halfOrientationFamily_of_det_pos`

This file sets up, for the target
`Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`, the basic language:

* `Work.PTGeometric.HOF.RelHmapOf` — the map `H_n(X, X∖K) → H_n(Y, Y∖K')` induced by a continuous
  map `f : X → Y` sending `X∖K` into `Y∖K'` (a map of pairs in the excluded-set convention);
* its functoriality and its naturality with respect to enlarging the excluded sets;
* homotopy invariance for such maps of pairs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.PTGeometric.HOF

noncomputable section

variable {X Y Z : TopCat} {n : ℕ}

/-- **The map on relative homology induced by a map of pairs**, in the excluded-set convention
(`Work.Orient.RelH X n K = H_n(X, X∖K)`): `f` has to send the complement of `K` into the complement
of `K'`. -/
def RelHmapOf (n : ℕ) (f : X ⟶ Y) (K : Set X) (K' : Set Y)
    (hf : ∀ x, x ∉ K → f x ∉ K') : Work.Orient.RelH X n K →ₗ[ℤ] Work.Orient.RelH Y n K' :=
  (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y Kᶜ K'ᶜ f
    (Work.Cohomology.relMapSub Kᶜ K'ᶜ f hf) (Work.Cohomology.relMapSub_spec Kᶜ K'ᶜ f hf)) n).hom

/-- The explicit form of `RelHmapOf`. -/
theorem RelHmapOf_eq (f : X ⟶ Y) (K : Set X) (K' : Set Y)
    (hf : ∀ x, x ∉ K → f x ∉ K') :
    RelHmapOf n f K K' hf
      = (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y Kᶜ K'ᶜ f
          (Work.Cohomology.relMapSub Kᶜ K'ᶜ f hf)
          (Work.Cohomology.relMapSub_spec Kᶜ K'ᶜ f hf)) n).hom := rfl

/-- `RelHmapOf` depends only on the two maps (not on the compatibility proof), and equal maps give
equal induced maps. -/
theorem RelHmapOf_congr {f f' : X ⟶ Y} (h : f = f') {K : Set X} {K' : Set Y}
    (hf : ∀ x, x ∉ K → f x ∉ K') (hf' : ∀ x, x ∉ K → f' x ∉ K') :
    RelHmapOf n f K K' hf = RelHmapOf n f' K K' hf' := by
  subst h
  congr 1

/-- The chain-level identity: `relChainsMapOf` of the identity is the identity. -/
theorem relChainsMapOf_id (X : TopCat) (A : Set X) :
    Work.Cohomology.relChainsMapOf X X A A (𝟙 X)
        (Work.Cohomology.relMapSub A A (𝟙 X) (fun x hx => hx))
        (Work.Cohomology.relMapSub_spec A A (𝟙 X) (fun x hx => hx))
      = 𝟙 (cokernel (Work.Cohomology.inclChains X A)) := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [Category.comp_id]
  rw [Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf]
  rw [Work.Cohomology.chainMap_id']
  rw [Category.id_comp]

/-- **The identity map induces the identity.** -/
theorem RelHmapOf_id (K : Set X) :
    RelHmapOf n (𝟙 X) K K (fun x hx => hx) = LinearMap.id := by
  apply LinearMap.ext
  intro x0
  rw [RelHmapOf_eq, relChainsMapOf_id]
  rw [show (𝟙 (cokernel (Work.Cohomology.inclChains X Kᶜ)))
      = 𝟙 (Work.Cohomology.relChains X Kᶜ) from rfl]
  rw [HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

/-- **Functoriality of `RelHmapOf`.** -/
theorem RelHmapOf_comp (f : X ⟶ Y) (g : Y ⟶ Z) {K : Set X} {K' : Set Y} {K'' : Set Z}
    (hf : ∀ x, x ∉ K → f x ∉ K') (hg : ∀ y, y ∉ K' → g y ∉ K'')
    (hgf : ∀ x, x ∉ K → (f ≫ g) x ∉ K'') :
    (RelHmapOf n g K' K'' hg).comp (RelHmapOf n f K K' hf)
      = RelHmapOf n (f ≫ g) K K'' hgf := by
  have key : (Work.Cohomology.relChainsMapOf X Y (Kᶜ) (K'ᶜ) f
        (Work.Cohomology.relMapSub (Kᶜ) (K'ᶜ) f hf)
        (Work.Cohomology.relMapSub_spec (Kᶜ) (K'ᶜ) f hf) :
      cokernel (Work.Cohomology.inclChains X (Kᶜ)) ⟶
        cokernel (Work.Cohomology.inclChains Y (K'ᶜ)))
      ≫ (Work.Cohomology.relChainsMapOf Y Z (K'ᶜ) (K''ᶜ) g
        (Work.Cohomology.relMapSub (K'ᶜ) (K''ᶜ) g hg)
        (Work.Cohomology.relMapSub_spec (K'ᶜ) (K''ᶜ) g hg) :
      cokernel (Work.Cohomology.inclChains Y (K'ᶜ)) ⟶
        cokernel (Work.Cohomology.inclChains Z (K''ᶜ)))
      = Work.Cohomology.relChainsMapOf X Z (Kᶜ) (K''ᶜ) (f ≫ g)
        (Work.Cohomology.relMapSub (Kᶜ) (K''ᶜ) (f ≫ g) hgf)
        (Work.Cohomology.relMapSub_spec (Kᶜ) (K''ᶜ) (f ≫ g) hgf) :=
    Work.RatHurewicz.Cofibre.relChainsMapOf_comp' (Kᶜ) (K'ᶜ) (K''ᶜ) f _ _ g _ _
  apply LinearMap.ext
  intro x0
  rw [RelHmapOf_eq, RelHmapOf_eq, RelHmapOf_eq, LinearMap.comp_apply]
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun (φ : Work.Cohomology.relChains X (Kᶜ) ⟶
      Work.Cohomology.relChains Z (K''ᶜ)) => (HomologicalComplex.homologyMap φ n).hom x0) key

/-- The naturality square of `relChainsMapOf` with respect to enlarging the excluded sets, at the
level of the relative chain complexes. -/
theorem relChainsMapOf_relCokerMap (f : X ⟶ Y) {K₁ K₂ : Set X} {K'₁ K'₂ : Set Y}
    (h : K₁ ⊆ K₂) (h' : K'₁ ⊆ K'₂)
    (g₂ : TopCat.of ↥(K₂ᶜ) ⟶ TopCat.of ↥(K'₂ᶜ))
    (w₂ : Work.Cohomology.subtypeIncl X (K₂ᶜ) ≫ f
      = g₂ ≫ Work.Cohomology.subtypeIncl Y (K'₂ᶜ))
    (g₁ : TopCat.of ↥(K₁ᶜ) ⟶ TopCat.of ↥(K'₁ᶜ))
    (w₁ : Work.Cohomology.subtypeIncl X (K₁ᶜ) ≫ f
      = g₁ ≫ Work.Cohomology.subtypeIncl Y (K'₁ᶜ)) :
    (Work.Cohomology.relChainsMapOf X Y (K₂ᶜ) (K'₂ᶜ) f g₂ w₂ :
        cokernel (Work.Cohomology.inclChains X (K₂ᶜ)) ⟶
          cokernel (Work.Cohomology.inclChains Y (K'₂ᶜ)))
        ≫ Work.Cohomology.relCokerMap Y (K'₂ᶜ) (K'₁ᶜ) (Set.compl_subset_compl.mpr h')
      = Work.Cohomology.relCokerMap X (K₂ᶜ) (K₁ᶜ) (Set.compl_subset_compl.mpr h)
        ≫ (Work.Cohomology.relChainsMapOf X Y (K₁ᶜ) (K'₁ᶜ) f g₁ w₁ :
          cokernel (Work.Cohomology.inclChains X (K₁ᶜ)) ⟶
            cokernel (Work.Cohomology.inclChains Y (K'₁ᶜ))) := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X (K₂ᶜ)))).mp
  rw [← Category.assoc, Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf, Category.assoc,
    Work.Cohomology.relCokerMap_comp_π]
  rw [← Category.assoc, Work.Cohomology.relCokerMap_comp_π,
    Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf]

/-- **Naturality of `RelHmapOf` with respect to enlarging the excluded sets.** -/
theorem RelHmapOf_resRelH (f : X ⟶ Y) {K₁ K₂ : Set X} {K'₁ K'₂ : Set Y} (h : K₁ ⊆ K₂)
    (h' : K'₁ ⊆ K'₂) (hf₂ : ∀ x, x ∉ K₂ → f x ∉ K'₂) (hf₁ : ∀ x, x ∉ K₁ → f x ∉ K'₁) :
    (RelHmapOf n f K₁ K'₁ hf₁).comp (Work.Orient.resRelH X n h)
      = (Work.Orient.resRelH Y n h').comp (RelHmapOf n f K₂ K'₂ hf₂) := by
  apply LinearMap.ext
  intro x0
  show (RelHmapOf n f K₁ K'₁ hf₁) ((Work.Orient.resRelH X n h) x0)
    = (Work.Orient.resRelH Y n h') ((RelHmapOf n f K₂ K'₂ hf₂) x0)
  rw [RelHmapOf_eq, RelHmapOf_eq]
  show (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y (K₁ᶜ) (K'₁ᶜ) f
        (Work.Cohomology.relMapSub (K₁ᶜ) (K'₁ᶜ) f hf₁)
        (Work.Cohomology.relMapSub_spec (K₁ᶜ) (K'₁ᶜ) f hf₁)) n).hom
      ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X (K₂ᶜ) (K₁ᶜ)
        (Set.compl_subset_compl.mpr h)) n).hom x0)
    = (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap Y (K'₂ᶜ) (K'₁ᶜ)
        (Set.compl_subset_compl.mpr h')) n).hom
      ((HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y (K₂ᶜ) (K'₂ᶜ) f
        (Work.Cohomology.relMapSub (K₂ᶜ) (K'₂ᶜ) f hf₂)
        (Work.Cohomology.relMapSub_spec (K₂ᶜ) (K'₂ᶜ) f hf₂)) n).hom x0)
  erw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    ← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun (φ : Work.Cohomology.relChains X (K₂ᶜ) ⟶
      Work.Cohomology.relChains Y (K'₁ᶜ)) => (HomologicalComplex.homologyMap φ n).hom x0)
    (relChainsMapOf_relCokerMap f h h' _ _ _ _).symm

/-- **Homotopy invariance of the induced map on relative homology.**  Two maps of pairs which are
homotopic through maps of pairs induce the same map on relative homology. -/
theorem relChainsMapOf_homologyMap_eq_of_homotopic {X Y : TopCat} (A : Set X) (B : Set Y)
    {f₀ f₁ : X ⟶ Y} (g₀ g₁ : TopCat.of ↥A ⟶ TopCat.of ↥B)
    (w₀ : Work.Cohomology.subtypeIncl X A ≫ f₀ = g₀ ≫ Work.Cohomology.subtypeIncl Y B)
    (w₁ : Work.Cohomology.subtypeIncl X A ≫ f₁ = g₁ ≫ Work.Cohomology.subtypeIncl Y B)
    (H : TopCat.Homotopy f₀ f₁) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y A B f₀ g₀ w₀) n
      = HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y A B f₁ g₁ w₁) n := by
  have hf₀ : ∀ x ∈ A, f₀ x ∈ B := by
    intro x hx
    have h : f₀ x = (g₀ ⟨x, hx⟩ : Y) := by
      have hw := congrArg (fun (φ : TopCat.of ↥A ⟶ Y) => φ ⟨x, hx⟩) w₀
      simp only [Work.Cohomology.subtypeIncl, TopCat.ofHom] at hw
      simpa using hw
    rw [h]
    exact (g₀ ⟨x, hx⟩).2
  have hf₁ : ∀ x ∈ A, f₁ x ∈ B := by
    intro x hx
    have h : f₁ x = (g₁ ⟨x, hx⟩ : Y) := by
      have hw := congrArg (fun (φ : TopCat.of ↥A ⟶ Y) => φ ⟨x, hx⟩) w₁
      simp only [Work.Cohomology.subtypeIncl, TopCat.ofHom] at hw
      simpa using hw
    rw [h]
    exact (g₁ ⟨x, hx⟩).2
  let hh : Homotopy (Work.Cohomology.chainMap ℤ X Y f₀) (Work.Cohomology.chainMap ℤ X Y f₁) :=
    H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
  refine Work.RatHurewicz.cokernelMap_homologyMap_eq
    (Work.Cohomology.inclChains X A) (Work.Cohomology.inclChains Y B) hh
    (fun i => ((Work.Thom.restrHomotopyTop H hf₀ hf₁ hH).toSSet.chainComplexMap
      (ModuleCat.of ℤ ℤ)).hom i (i+1)) (fun i => ?_)
    (Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf A B f₀ g₀ w₀)
    (Work.RatHurewicz.Cofibre.cokernel_π_relChainsMapOf A B f₁ g₁ w₁) n
  exact (Work.Thom.prism_preserves H hf₀ hf₁ hH ℤ i).symm

/-- **Homotopy invariance of `RelHmapOf`** for maps of pairs. -/
theorem RelHmapOf_homotopic {f₀ f₁ : X ⟶ Y} {K : Set X} {K' : Set Y}
    (hf₀ : ∀ x, x ∉ K → f₀ x ∉ K') (hf₁ : ∀ x, x ∉ K → f₁ x ∉ K')
    (H : TopCat.Homotopy f₀ f₁) (hH : ∀ t x, x ∉ K → H (t, x) ∉ K') :
    RelHmapOf n f₀ K K' hf₀ = RelHmapOf n f₁ K K' hf₁ := by
  apply LinearMap.ext
  intro x0
  rw [RelHmapOf_eq, RelHmapOf_eq]
  exact LinearMap.congr_fun (congrArg (fun ψ => ModuleCat.Hom.hom ψ)
    (relChainsMapOf_homologyMap_eq_of_homotopic (Kᶜ) (K'ᶜ)
      (Work.Cohomology.relMapSub (Kᶜ) (K'ᶜ) f₀ hf₀) (Work.Cohomology.relMapSub (Kᶜ) (K'ᶜ) f₁ hf₁)
      (Work.Cohomology.relMapSub_spec (Kᶜ) (K'ᶜ) f₀ hf₀)
      (Work.Cohomology.relMapSub_spec (Kᶜ) (K'ᶜ) f₁ hf₁) H (fun t x hx => hH t x hx) n)) x0

end

end Work.PTGeometric.HOF
