import Mathlib
import Submission.Work.Cohomology.capped_rel_cupSquare_ne_zero
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsMap_quasiIso
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.collarInclCohomologyIsIso
import Submission.Work.Cohomology.PairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary lemmas for `Work.Cohomology.capRelMap_isIso`

This file reproduces, in the part of the library that is compatible with
`Work.Milnor.cappedDatum` (i.e. whose import closure avoids `Work.Cohomology.dualZ`, which clashes
with `localCohomology`), the generalities about the relative pair map `relComplexMap` and the
duality identification of the relative cochains with the dual of the relative chains, together
with the resulting **cochain-level excision** for an open cover.

The main outputs are

* `Work.Cohomology.capRel_relComplexMap_comp`, `..._id`, `..._congr` — functoriality of the pair
  map on relative cochains;
* `Work.Cohomology.capRel_relComplexMap_iso_of_isIso_pairs` — a homeomorphism of pairs induces an
  isomorphism on relative cohomology;
* `Work.Cohomology.capRel_dualComplex_nat` — the pair map on relative cochains is, under
  `capRelDualIsoComplex`, the dual of the pair map on relative chains;
* `Work.Cohomology.capRel_excision_isIso` — the inclusion of pairs `(U, U ∩ A) → (X, A)` induces an
  isomorphism on relative cohomology when `U, A` are open and cover `X`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
noncomputable section

/-! ## The duality identification as a single cochain map -/

/-- The duality identification `dualComplex ℤ (relChains X A) ≅ relComplex ℤ X A`, assembled from
the degreewise isomorphisms `relDualIso`. -/
def capRelDualIsoComplex (X : TopCat) (A : Set X) :
    dualComplex ℤ (relChains X A) ≅ relComplex ℤ X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => relDualIso X A n)
    (fun i j hij => by rw [← hij]; exact relDualIso_comm X A i)

@[simp] theorem capRelDualIsoComplex_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (capRelDualIsoComplex X A).hom.f n = (relDualIso X A n).hom :=
  HomologicalComplex.Hom.isoOfComponents_hom_f _ _ n

@[simp] theorem capRelDualIsoComplex_inv_f (X : TopCat) (A : Set X) (n : ℕ) :
    (capRelDualIsoComplex X A).inv.f n = (relDualIso X A n).inv :=
  HomologicalComplex.Hom.isoOfComponents_inv_f _ _ n

/-- The `n`-th component of `dualChainMap` is the `n`-th component of the dual of `chainMap`. -/
theorem capRel_dualChainMap_f (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    (dualChainMap ℤ X Y f).f n
      = dualComplexMapComp ℤ (singularChains ℤ X) (singularChains ℤ Y)
          (chainMap ℤ X Y f) n := rfl

/-- `dualChainMap` is the dual of `chainMap`, as a cochain map. -/
theorem capRel_dualChainMap (X Y : TopCat) (f : X ⟶ Y) :
    dualChainMap ℤ X Y f = dualComplexMap ℤ (singularChains ℤ X) (singularChains ℤ Y)
      (chainMap ℤ X Y f) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [dualComplexMap_f]
  exact capRel_dualChainMap_f X Y f n

/-- The relation between the degreewise duality isomorphism and the inclusion of the relative
cochains into the absolute ones, as a cochain map. -/
theorem capRel_dualIso_comp_relIncl (X : TopCat) (A : Set X) :
    (capRelDualIsoComplex X A).hom ≫ relIncl ℤ X A
      = dualComplexMap ℤ (singularChains ℤ X) (relChains X A)
          (cokernel.π (inclChains X A)) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, capRelDualIsoComplex_hom_f, relIncl_f, dualComplexMap_f,
    relDualIso_hom]
  exact relDualMap_comp_relIncl X A n

/-- The inclusion of the relative cochains into the absolute cochains is a monomorphism. -/
theorem capRel_relIncl_mono (X : TopCat) (A : Set X) : Mono (relIncl ℤ X A) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [relIncl_f, ModuleCat.mono_iff_injective]
  exact Subtype.val_injective

/-! ## Functoriality of the pair map on relative cochains -/

/-- The pair map only depends on the map of spaces, not on the proof that it carries `A₁` into
`A₂`. -/
theorem capRel_relComplexMap_congr (R : Type) [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
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

/-- **The pair map is functorial: the identity.** -/
theorem capRel_relComplexMap_id (R : Type) [CommRing R] {X : TopCat} (A : Set X)
    (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap R A A (𝟙 X) h = 𝟙 (relComplex R X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, relMapLM_coe, dualChainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- **The pair map is functorial: composition.** -/
theorem capRel_relComplexMap_comp (R : Type) [CommRing R] {X₀ X₁ X₂ : TopCat} (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) :
    relComplexMap R A₀ A₂ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = relComplexMap R A₁ A₂ g hg ≫ relComplexMap R A₀ A₁ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relComplexMap_f, relComplexMap_f, relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply, relMapLM_coe,
    dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

/-- **A map of pairs which is an isomorphism of the underlying spaces is an isomorphism on relative
cohomology.** -/
theorem capRel_relComplexMap_iso_of_isIso_pairs (R : Type) [CommRing R] {X₁ X₂ : TopCat}
    (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (g : X₂ ⟶ X₁)
    (hg : ∀ y ∈ A₂, g y ∈ A₁)
    (hfg : CategoryTheory.CategoryStruct.comp f g = CategoryTheory.CategoryStruct.id X₁)
    (hgf : CategoryTheory.CategoryStruct.comp g f = CategoryTheory.CategoryStruct.id X₂)
    (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ f h) n) := by
  have h1 : CategoryTheory.CategoryStruct.comp (relComplexMap R A₁ A₂ f h)
      (relComplexMap R A₂ A₁ g hg) = CategoryTheory.CategoryStruct.id (relComplex R X₂ A₂) := by
    rw [← capRel_relComplexMap_comp R A₂ A₁ A₂ g f hg h]
    refine (capRel_relComplexMap_congr R A₂ A₂ hgf (fun x hx => h (g x) (hg x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact capRel_relComplexMap_id R A₂ (fun x hx => by simpa using hx)
  have h2 : CategoryTheory.CategoryStruct.comp (relComplexMap R A₂ A₁ g hg)
      (relComplexMap R A₁ A₂ f h) = CategoryTheory.CategoryStruct.id (relComplex R X₁ A₁) := by
    rw [← capRel_relComplexMap_comp R A₁ A₂ A₁ f g h hg]
    refine (capRel_relComplexMap_congr R A₁ A₁ hfg (fun x hx => hg (f x) (h x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact capRel_relComplexMap_id R A₁ (fun x hx => by simpa using hx)
  haveI : CategoryTheory.IsIso (relComplexMap R A₁ A₂ f h) :=
    ⟨relComplexMap R A₂ A₁ g hg, h1, h2⟩
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
    (relComplexMap R A₁ A₂ f h)

/-- **The pair map of a composite is an isomorphism on relative cohomology when both factors
are.** -/
theorem capRel_isIso_relComplexMap_comp (R : Type) [CommRing R] {X₀ X₁ X₂ : TopCat}
    (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂) (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
    (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) (n : ℕ)
    (h : ∀ x ∈ A₀, (CategoryTheory.CategoryStruct.comp f g) x ∈ A₂)
    (h₂ : CategoryTheory.IsIso (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ g hg) n))
    (h₁ : CategoryTheory.IsIso (HomologicalComplex.homologyMap (relComplexMap R A₀ A₁ f hf) n)) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relComplexMap R A₀ A₂
        (CategoryTheory.CategoryStruct.comp f g) h) n) := by
  have heq : relComplexMap R A₀ A₂ (CategoryTheory.CategoryStruct.comp f g) h
      = relComplexMap R A₀ A₂ (CategoryTheory.CategoryStruct.comp f g)
          (fun x hx => hg (f x) (hf x hx)) :=
    capRel_relComplexMap_congr R A₀ A₂ rfl h (fun x hx => hg (f x) (hf x hx))
  rw [heq, capRel_relComplexMap_comp R A₀ A₁ A₂ f g hf hg, HomologicalComplex.homologyMap_comp]
  exact inferInstance

/-! ## The chain-level identity behind the naturality of the duality -/

/-- The composite `cokernel.π ≫ relChainsMapOf` is the chain map followed by `cokernel.π`. -/
theorem capRel_cokernel_π_relChainsMapOf {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B) (w : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    cokernel.π (inclChains X A) ≫ relChainsMapOf X Y A B f g w
      = chainMap ℤ X Y f ≫ cokernel.π (inclChains Y B) := by
  rw [relChainsMapOf]
  exact cokernel_π_map (inclChains X A) (inclChains Y B)
    (chainMap ℤ (TopCat.of A) (TopCat.of B) g) (chainMap ℤ X Y f) _

/-- The pair map `(U, U ∩ A) → (X, A)` in the `relMapSub` normal form is `relChainsMap`. -/
theorem capRel_relChainsMapOf_relMapSub_eq_relChainsMap (X : TopCat) (U A : Set X)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A}, (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    relChainsMapOf (TopCat.of U) X {y : U | (y : X) ∈ A} A (subtypeIncl X U)
        (relMapSub {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)
        (relMapSub_spec {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)
      = relChainsMap X U A := by
  rw [relChainsMap]
  apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) {y : U | (y : X) ∈ A}))).1
  rw [capRel_cokernel_π_relChainsMapOf, capRel_cokernel_π_relChainsMapOf]

/-! ## Naturality of the duality identification with respect to the pair map -/

/-- **The pair map on relative cochains is the dual of the pair map on relative chains.**  Under
the duality identifications `capRelDualIsoComplex`, the contravariant map `relComplexMap` induced
by a map of pairs corresponds to the contravariant map `dualComplexMap` induced by the
corresponding map of relative chain complexes. -/
theorem capRel_dualComplex_nat {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h
      = (capRelDualIsoComplex X₂ A₂).inv
        ≫ dualComplexMap ℤ (relChains X₁ A₁) (relChains X₂ A₂)
            (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h))
        ≫ (capRelDualIsoComplex X₁ A₁).hom := by
  classical
  have key1 : ∀ (X : TopCat) (A : Set X),
      (capRelDualIsoComplex X A).hom ≫ relIncl ℤ X A
        = dualComplexMap ℤ (singularChains ℤ X) (relChains X A)
            (cokernel.π (inclChains X A)) := fun X A => capRel_dualIso_comp_relIncl X A
  have key3 : dualChainMap ℤ X₁ X₂ f
      = dualComplexMap ℤ (singularChains ℤ X₁) (singularChains ℤ X₂)
          (chainMap ℤ X₁ X₂ f) := capRel_dualChainMap X₁ X₂ f
  have key4 : cokernel.π (inclChains X₁ A₁)
        ≫ relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h)
      = chainMap ℤ X₁ X₂ f ≫ cokernel.π (inclChains X₂ A₂) :=
    capRel_cokernel_π_relChainsMapOf A₁ A₂ f _ _
  haveI : Mono (relIncl ℤ X₁ A₁) := capRel_relIncl_mono X₁ A₁
  refine (cancel_epi (capRelDualIsoComplex X₂ A₂).hom).1 ?_
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine (cancel_mono (relIncl ℤ X₁ A₁)).1 ?_
  rw [Category.assoc, Category.assoc]
  rw [relComplexMap_comp_relIncl, key1 X₁ A₁]
  rw [← Category.assoc, key1 X₂ A₂]
  rw [key3, ← dualComplexMap_comp, ← dualComplexMap_comp]
  rw [key4]

/-! ## Cochain-level excision -/

/-- **The inclusion of pairs `(U, U ∩ A) → (X, A)` induces an isomorphism on relative cohomology**
whenever `U, A` are open and cover `X`. -/
theorem capRel_excision_isIso (X : TopCat) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (n : ℕ)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A},
      (ConcreteCategory.hom (subtypeIncl X U)) x ∈ A) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ {y : U | (y : X) ∈ A} A (subtypeIncl X U) h) n) := by
  rw [capRel_dualComplex_nat, capRel_relChainsMapOf_relMapSub_eq_relChainsMap,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI hqc : ∀ i, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relChainsMap X U A) i) :=
    fun i => relChainsMap_quasiIso X U A hU hA hcov i
  haveI hdual : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (relChains (TopCat.of U) {y : U | (y : X) ∈ A}) (relChains X A)
        (relChainsMap X U A)) n) :=
    dualComplexMap_quasiIso (relChainsMap X U A)
      (fun i => relChainsProjective (TopCat.of U) {y : U | (y : X) ∈ A} i)
      (fun i => relChainsProjective X A i) hqc n
  infer_instance

/-! ## The collar step -/

/-- **The inclusion of pairs `(Vk(-2), Mk(-2)) → (Vk(-2), collar(-2))` is an isomorphism on
relative cohomology.** -/
theorem capRel_collar_isIso (n : ℕ)
    (h : ∀ x ∈ (Set.range (Work.Milnor.mkToVkFun (-2)) : Set (Submission.Milnor.Vk (-2))),
      (𝟙 (TopCat.of (Submission.Milnor.Vk (-2)))) x ∈ Work.Milnor.collar (-2)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relComplexMap ℤ (Set.range (Work.Milnor.mkToVkFun (-2))) (Work.Milnor.collar (-2))
        (𝟙 (TopCat.of (Submission.Milnor.Vk (-2)))) h) n) := by
  classical
  let X : TopCat := TopCat.of (Submission.Milnor.Vk (-2))
  let A₁ : Set X := Set.range (Work.Milnor.mkToVkFun (-2))
  let A₂ : Set X := Work.Milnor.collar (-2)
  have h' : ∀ x ∈ A₁, (𝟙 X) x ∈ A₂ := h
  let φ : pairShort ℤ X A₂ ⟶ pairShort ℤ X A₁ :=
    ShortComplex.homMk (relComplexMap ℤ A₁ A₂ (𝟙 X) h')
      (𝟙 (singularCochainComplex ℤ X))
      (dualChainMap ℤ (TopCat.of ↥A₁) (TopCat.of ↥A₂) (relMapSub A₁ A₂ (𝟙 X) h'))
      (by
        have hh := relComplexMap_comp_relIncl (R := ℤ) A₁ A₂ (𝟙 X) h'
        rwa [dualChainMap_id] at hh)
      (by
        show (𝟙 (singularCochainComplex ℤ X)) ≫ restr ℤ X A₁
          = restr ℤ X A₂ ≫ dualChainMap ℤ (TopCat.of ↥A₁) (TopCat.of ↥A₂)
              (relMapSub A₁ A₂ (𝟙 X) h')
        rw [Category.id_comp]
        have hh := dualChainMap_restr_comp ℤ A₁ A₂ (𝟙 X) h'
        rwa [dualChainMap_id] at hh)
  have h₂ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₂ k) := by
    intro k
    have hh : CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (𝟙 (singularCochainComplex ℤ X)) k) := by
      rw [HomologicalComplex.homologyMap_id]
      infer_instance
    exact hh
  have h₃ : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ k) := by
    intro k
    exact collarInclCohomologyIsIso h' k
  exact isIso_homologyMap_tau1 ℤ φ (pairShort_shortExact ℤ X A₂)
    (pairShort_shortExact ℤ X A₁) h₂ h₃ n

end
end Work.Cohomology
