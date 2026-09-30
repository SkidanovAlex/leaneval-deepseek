import Mathlib
import Submission.Work.Pi6.SQM.SIG.Apply
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# SQM / SIG — the map of pairs induced by a based map, and naturality data for `σ`

This file collects the definitions used in the proof of naturality of the cohomology suspension
`σ = δ⁻¹ ∘ q* ∘ ρ` (`Work.Pi6.SQM.SIG.sigmaNatural`), together with a few elementary invocations of
the functoriality of the relative pair map `Work.Cohomology.relComplexMap` (reproved here in order
to avoid pulling in the whole Milnor/capped-space development).

For a continuous map `h : C(K,L)` and a base point `k₀ : K`:

* `pathMap K L k₀ h : C(PK K k₀, PK L (h k₀))` is the map on based path spaces `γ ↦ h ∘ γ`;
* `PKmap K L k₀ h` is the same map as a morphism of `TopCat`, and
  `PKmap_evalOne` records that it commutes with `evalOne` and `h`;
* `fibreMap K L k₀ h` is the induced map on the fibres of `evalOne`, i.e. the map
  `fibre (evalOne K k₀) k₀ → fibre (evalOne L (h k₀)) (h k₀)`;
* `basePairMap`, `pathPairMap` are the induced maps of pairs on relative cochain complexes
  `C^*(L,{h k₀}) → C^*(K,{k₀})` and `C^*(PL, fibre L) → C^*(PK, fibre K)`.
-/

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

abbrev F2' : Type := Work.Pi6.SQ.F2

/-! ## The map on path spaces induced by `h` -/

/-- The map on based path spaces induced by `h`: `γ ↦ h ∘ γ`. -/
def pathMap (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) :
    C(PK K k₀, PK L (h k₀)) where
  toFun γ := ⟨h.comp γ.1, by rw [ContinuousMap.comp_apply, γ.2]⟩
  continuous_toFun := by fun_prop

/-- `pathMap` intertwines the evaluations: `evalOne L ∘ pathMap = h ∘ evalOne K`. -/
theorem pathMap_evalOne (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K)
    (h : C(K, L)) :
    (Work.StemsB.evalOne L (h k₀)).comp (pathMap K L k₀ h) =
      h.comp (Work.StemsB.evalOne K k₀) := by
  ext γ
  rfl

/-- `pathMap` carries the fibre of `evalOne K k₀` into the fibre of `evalOne L (h k₀)`. -/
theorem pathMap_mem (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L))
    (γ : PK K k₀) (hγ : γ ∈ fibreSet K k₀) : pathMap K L k₀ h γ ∈ fibreSet L (h k₀) := by
  have h2 : Work.StemsB.evalOne L (h k₀) (pathMap K L k₀ h γ) = h (Work.StemsB.evalOne K k₀ γ) :=
    rfl
  rw [fibreSet, Set.mem_ofPred_eq, h2, hγ]

/-- The map of pairs `(PK K, fibre K) → (PK L, fibre L)` induced by `h`, as a morphism of
`TopCat`. -/
def PKmap (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) :
    TopCat.of (PK K k₀) ⟶ TopCat.of (PK L (h k₀)) := TopCat.ofHom (pathMap K L k₀ h)

/-- `PKmap` commutes with `evalOne` and `h`, as morphisms of `TopCat`. -/
theorem PKmap_evalOne (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K)
    (h : C(K, L)) :
    PKmap K L k₀ h ≫ TopCat.ofHom (Work.StemsB.evalOne L (h k₀)) =
      TopCat.ofHom (Work.StemsB.evalOne K k₀) ≫ TopCat.ofHom h :=
  congrArg TopCat.ofHom (pathMap_evalOne K L k₀ h)

/-- The induced map on the fibres of `evalOne`. -/
def fibreMap (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) :
    TopCat.of ↥(fibreSet K k₀) ⟶ TopCat.of ↥(fibreSet L (h k₀)) :=
  relMapSub (fibreSet K k₀) (fibreSet L (h k₀)) (PKmap K L k₀ h)
    (fun x hx => pathMap_mem K L k₀ h x hx)

/-! ## The pair maps on relative cochain complexes -/

/-- The map of pairs `(K,{k₀}) → (L,{h k₀})` on relative cochains. -/
def basePairMap (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) :
    relComplex Work.Pi6.SQ.F2 (TopCat.of L) ({h k₀} : Set L) ⟶
      relComplex Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K) :=
  relComplexMap Work.Pi6.SQ.F2 (X₁ := TopCat.of K) (X₂ := TopCat.of L)
    ({k₀} : Set K) ({h k₀} : Set L) (TopCat.ofHom h)
    (fun x hx => by simpa [Set.mem_singleton_iff] using congrArg h hx)

/-- The map of pairs `(PK K, fibre K) → (PK L, fibre L)` on relative cochains. -/
def pathPairMap (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) :
    relComplex Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) ⟶
      relComplex Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) :=
  relComplexMap Work.Pi6.SQ.F2 (X₁ := TopCat.of (PK K k₀)) (X₂ := TopCat.of (PK L (h k₀)))
    (fibreSet K k₀) (fibreSet L (h k₀))
    (TopCat.ofHom (pathMap K L k₀ h)) (fun x hx => pathMap_mem K L k₀ h x hx)

/-! ## Functoriality of the pair map, reproved locally -/

theorem lmComp (R : Type) [CommRing R] {X₀ X₁ X₂ : TopCat} (A₀ : Set X₀) (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (hf : ∀ x ∈ A₀, f x ∈ A₁)
    (hg : ∀ y ∈ A₁, g y ∈ A₂) :
    relComplexMap R A₀ A₂ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = relComplexMap R A₁ A₂ g hg ≫ relComplexMap R A₀ A₁ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relComplexMap_f R A₀ A₂ (f ≫ g) _ n,
    relComplexMap_f R A₁ A₂ g hg n, relComplexMap_f R A₀ A₁ f hf n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply, relMapLM_coe,
    dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

theorem lmCongr (R : Type) [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    {f f' : X₁ ⟶ X₂} (hf : f = f') (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, f' x ∈ A₂) :
    relComplexMap R A₁ A₂ f h = relComplexMap R A₁ A₂ f' h' := by
  subst hf
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem lmCompRelIncl (R : Type) [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap R A₁ A₂ f h ≫ relIncl R X₁ A₁ = relIncl R X₂ A₂ ≫ dualChainMap R X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relComplexMap_f, relIncl_f, relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact relMapLM_coe R A₁ A₂ f h n x

/-- `pairMapK` is the pair map of `evalOne`. -/
theorem pairMapK_eq (K : Type) [TopologicalSpace K] (k₀ : K) :
    pairMapK K k₀ = relComplexMap Work.Pi6.SQ.F2 (X₁ := TopCat.of (PK K k₀)) (X₂ := TopCat.of K)
      (fibreSet K k₀) ({k₀} : Set K)
      (TopCat.ofHom (Work.StemsB.evalOne K k₀)) (fun x hx => hx) := rfl

end

end Work.Pi6.SQM.SIG
