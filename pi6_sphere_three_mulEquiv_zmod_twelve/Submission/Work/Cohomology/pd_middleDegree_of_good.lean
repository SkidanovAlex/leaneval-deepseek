import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.relCapPair_empty_eq_capPair
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.Crux.relCapPair_natural
import Submission.Work.Cohomology.pd_goodD_natural

set_option synthInstance.maxHeartbeats 400000

/-!
# The final degree reduction of the `Good` framework

`Work.Cohomology.Good N c W hW` is the elementwise form of "the duality map with compact supports
`H^k_c(W) → H_{N-k}(W)`, `x ↦ x ⌢ μ_W`, is bijective" (see `Work.Cohomology.pd_good`).

This file proves the final reduction: from `Good (n+n) c Set.univ isOpen_univ` (the `Good` predicate
for the whole space at the fundamental class `c ∈ H_{n+n}(M)`) one gets the bijectivity of the
absolute cap product

`y ↦ y ⌢ c : H^n(M; ℤ) → H_n(M; ℤ)`

of Poincaré–Lefschetz duality in the middle degree.

The proof has three steps.

* The `Good` predicate at `W = Set.univ` gives bijectivity of `goodD` at the maximal compact set
  `K = Set.univ` (where the filtered colimit degenerates to the module itself; the transition maps at
  the top are the identity, `pdRelComplexEnlarge_self`).
* The pair `(Set.univ, Set.univ∖Set.univ)` is identified — by the canonical homeomorphism
  `Set.univ ≅ M` — with the pair `(M, M∖Set.univ)`, and `Crux.relCapPair_natural` transfers the
  bijectivity of `goodD` for the first pair to bijectivity of the cap product with the local class
  `relLocClass M (n+n) c Set.univ` for the second.
* `relCapPair_abs_eq_capPair` (the relative cap product with a class coming from an absolute cycle
  is the absolute cap product) together with the isomorphism
  `relIncl ℤ M (Set.univ)ᶜ : C^*(M, M∖Set.univ) ≅ C^*(M)` gives the final statement.
-/

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits


namespace Work.Cohomology

noncomputable section

/-! ## The relative cap product with an absolute cycle is the absolute cap product

For `x ∈ H^n(X,A;ℤ)` and an absolute class `c ∈ H_{n+m}(X;ℤ)`, capping `x` with the image of `c`
in `H_{n+m}(X,A;ℤ)` gives the same result as first pushing `x` to the absolute cohomology and then
capping with `c`.  This is the (slightly more general) form of
`Work.Cohomology.relCapPair_empty_eq_capPair`. -/
set_option backward.isDefEq.respectTransparency false in
theorem relCapPair_abs_eq_capPair (X : TopCat) (A : Set X) (n m : ℕ)
    (x : (Work.Cohomology.relComplex ℤ X A).homology n)
    (c : (Work.Cohomology.singularChains ℤ X).homology (n + m)) :
    (Work.Cohomology.relCapPair (TopCat.of X) A n m) x
        ((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) (n + m)) c)
      = (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj X) n m)
          ((HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) n) x) c := by
  change (relCapPair X A n m) x
        ((HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (n + m)) c)
      = (capPair ℤ (TopCat.toSSet.obj X) n m)
          ((HomologicalComplex.homologyMap (relIncl ℤ X A) n) x) c
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relComplex ℤ X A).homologyπ n)).mp inferInstance x
  obtain ⟨c₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((singularChains ℤ X).homologyπ (n + m))).mp inferInstance c
  have hc : (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (n + m))
      ((singularChains ℤ X).homologyπ (n + m) c₀)
      = (relChains X A).homologyπ (n + m)
          (HomologicalComplex.cyclesMap (cokernel.π (inclChains X A)) (n + m) c₀) :=
    congrArg (fun g => g.hom c₀)
      (HomologicalComplex.homologyπ_naturality (φ := cokernel.π (inclChains X A)) (n + m))
  have hx : (HomologicalComplex.homologyMap (relIncl ℤ X A) n)
      ((relComplex ℤ X A).homologyπ n z)
      = (singularCochainComplex ℤ X).homologyπ n
          (HomologicalComplex.cyclesMap (relIncl ℤ X A) n z) :=
    congrArg (fun g => g.hom z)
      (HomologicalComplex.homologyπ_naturality (φ := relIncl ℤ X A) n)
  rw [hc, hx]
  rw [relCapPair_apply]
  change (singularChains ℤ X).homologyπ m
        (relCapPairZ X A n m z
          (HomologicalComplex.cyclesMap (cokernel.π (inclChains X A)) (n + m) c₀))
      = (capPair ℤ (TopCat.toSSet.obj X) n m)
          (((cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n)
            (HomologicalComplex.cyclesMap (relIncl ℤ X A) n z))
          (((chainC ℤ (TopCat.toSSet.obj X)).homologyπ (n + m)) c₀)
  rw [capPair_apply]
  have hAB : relCapPairZ X A n m z
        (HomologicalComplex.cyclesMap (cokernel.π (inclChains X A)) (n + m) c₀)
      = capPairZ ℤ (TopCat.toSSet.obj X) n m
          (HomologicalComplex.cyclesMap (relIncl ℤ X A) n z) c₀ := by
    apply iCycles_injective_C ℤ (singularChains ℤ X) m
    change (singularChains ℤ X).iCycles m
          (relCapPairZ X A n m z
            (HomologicalComplex.cyclesMap (cokernel.π (inclChains X A)) (n + m) c₀))
        = (chainC ℤ (TopCat.toSSet.obj X)).iCycles m
            (capPairZ ℤ (TopCat.toSSet.obj X) n m
              (HomologicalComplex.cyclesMap (relIncl ℤ X A) n z) c₀)
    rw [relCapPairZ_iCycles, capPairZ_iCycles]
    have hcyc₁ : (relChains X A).iCycles (n + m)
          (HomologicalComplex.cyclesMap (cokernel.π (inclChains X A)) (n + m) c₀)
        = ((cokernel.π (inclChains X A)).f (n + m)) ((singularChains ℤ X).iCycles (n + m) c₀) :=
      congrArg (fun g => g.hom c₀)
        (HomologicalComplex.cyclesMap_i (cokernel.π (inclChains X A)) (n + m))
    have hcyc₂ : (cochainC ℤ (TopCat.toSSet.obj X)).iCycles n
          (HomologicalComplex.cyclesMap (relIncl ℤ X A) n z)
        = ((relIncl ℤ X A).f n) ((relComplex ℤ X A).iCycles n z) :=
      congrArg (fun g => g.hom z)
        (HomologicalComplex.cyclesMap_i (relIncl ℤ X A) n)
    rw [hcyc₁, hcyc₂]
    rw [relChains_cokernelIso_canon_apply, relCapHalf_apply_incl, relIncl_f]
    simp only [ModuleCat.hom_ofHom]
    rfl
  rw [hAB]
  rfl

/-! ## Functoriality of the pair map on relative cochains (local copies)

These three lemmas and `pdmd_relComplexMap_iso_of_isIso_pairs` are copies of results in
`Submission/Work/Cohomology/cappedPairDefs.lean` / `cappedPairMapIso.lean`; they are reproduced here
because those modules are not importable together with `pd_good` (the two worlds both define
`Work.Cohomology.dualZ`). -/

set_option backward.isDefEq.respectTransparency false in
theorem pdmd_relComplexMap_congr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) {f f' : X₁ ⟶ X₂}
    (hf : f = f') (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, f' x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f' h' := by
  subst hf
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pdmd_relComplexMap_id {X : TopCat} (A : Set X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A) :
    relComplexMap ℤ A A (𝟙 X) h = 𝟙 (relComplex ℤ X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [relComplexMap_f ℤ A A (𝟙 X) h n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, relMapLM_coe, dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pdmd_relComplexMap_comp {X₀ X₁ X₂ : TopCat} (A₀ : Set X₀) (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (hf : ∀ x ∈ A₀, f x ∈ A₁) (hg : ∀ y ∈ A₁, g y ∈ A₂) :
    relComplexMap ℤ A₀ A₂ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = relComplexMap ℤ A₁ A₂ g hg ≫ relComplexMap ℤ A₀ A₁ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, relComplexMap_f ℤ A₀ A₂ (f ≫ g) _ n,
    relComplexMap_f ℤ A₁ A₂ g hg n, relComplexMap_f ℤ A₀ A₁ f hf n]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply, relMapLM_coe,
    dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **A map of pairs which is an isomorphism of the underlying spaces is an isomorphism on relative
cohomology.** -/
theorem pdmd_relComplexMap_iso_of_isIso_pairs {X₁ X₂ : TopCat}
    (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (g : X₂ ⟶ X₁)
    (hg : ∀ y ∈ A₂, g y ∈ A₁)
    (hfg : CategoryTheory.CategoryStruct.comp f g = CategoryTheory.CategoryStruct.id X₁)
    (hgf : CategoryTheory.CategoryStruct.comp g f = CategoryTheory.CategoryStruct.id X₂)
    (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ f h) n) := by
  have h1 : CategoryTheory.CategoryStruct.comp (relComplexMap ℤ A₁ A₂ f h)
      (relComplexMap ℤ A₂ A₁ g hg) = CategoryTheory.CategoryStruct.id (relComplex ℤ X₂ A₂) := by
    rw [← pdmd_relComplexMap_comp A₂ A₁ A₂ g f hg h]
    refine (pdmd_relComplexMap_congr A₂ A₂ hgf (fun x hx => h (g x) (hg x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact pdmd_relComplexMap_id A₂ (fun x hx => by simpa using hx)
  have h2 : CategoryTheory.CategoryStruct.comp (relComplexMap ℤ A₂ A₁ g hg)
      (relComplexMap ℤ A₁ A₂ f h) = CategoryTheory.CategoryStruct.id (relComplex ℤ X₁ A₁) := by
    rw [← pdmd_relComplexMap_comp A₁ A₂ A₁ f g h hg]
    refine (pdmd_relComplexMap_congr A₁ A₁ hfg (fun x hx => hg (f x) (h x hx))
      (fun x hx => by simpa using hx)).trans ?_
    exact pdmd_relComplexMap_id A₁ (fun x hx => by simpa using hx)
  haveI : CategoryTheory.IsIso (relComplexMap ℤ A₁ A₂ f h) :=
    ⟨relComplexMap ℤ A₂ A₁ g hg, h1, h2⟩
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
    (relComplexMap ℤ A₁ A₂ f h)

/-! ## The enlargement map at `K = K'` is the identity -/

set_option backward.isDefEq.respectTransparency false in
lemma pdRelComplexEnlarge_self {M : TopCat} (W : Set M) {K : Set M} (h : K ⊆ K) :
    pdRelComplexEnlarge W h = 𝟙 (relComplex ℤ (TopCat.of W) (pdRelSub W K)) := by
  have hbridge : pdRelComplexEnlarge W h
      = relComplexMap ℤ (pdRelSub W K) (pdRelSub W K) (𝟙 (TopCat.of W))
          (pdRelSub_mono_id h) := by
    rw [pdRelComplexEnlarge]
  rw [hbridge]
  exact pdmd_relComplexMap_id (X := TopCat.of W) (pdRelSub W K) (pdRelSub_mono_id h)

/-! ## The two spellings of the inclusion of pairs `(U, U∩A) ⊆ (X, A)` -/

set_option backward.isDefEq.respectTransparency false in
theorem pdmd_relChainsMapOf_relMapSub_eq_relChainsMap (X : TopCat) (U A : Set X)
    (h : ∀ x ∈ {y : U | (y : X) ∈ A}, (subtypeIncl X U) x ∈ A) :
    relChainsMapOf (TopCat.of U) X {y : U | (y : X) ∈ A} A (subtypeIncl X U)
        (relMapSub {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)
        (relMapSub_spec {y : U | (y : X) ∈ A} A (subtypeIncl X U) h)
      = relChainsMap X U A := by
  rw [relChainsMap]
  apply (cancel_epi (cokernel.π (inclChains (TopCat.of U) {y : U | (y : X) ∈ A}))).1
  rw [Crux.cruxCokernel_π_relChainsMapOf, Crux.cruxCokernel_π_relChainsMapOf]

/-! ## The singular complexes of an empty subspace -/

lemma isEmpty_singularSimplex_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquivT Y (Opposite.op (SimplexCategory.mk n))) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op (SimplexCategory.mk n))).len + 1)))) :=
    inferInstance
  exact isEmptyElim (hx (Classical.arbitrary _))

lemma isZero_singularChains_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((singularChains ℤ Y).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) :=
    isEmpty_singularSimplex_of_isEmpty Y n
  exact isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) => ModuleCat.of ℤ ℤ)

lemma isZero_singularCochainComplex_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((singularCochainComplex ℤ Y).X n) :=
  isZero_dualObj_of_isZero ℤ (singularChains ℤ Y)
    (fun m => isZero_singularChains_of_isEmpty Y m) n

lemma restr_eq_zero_of_isEmpty (X : TopCat) (A : Set X) [IsEmpty (↥A)] (n : ℕ) :
    (restr ℤ X A).f n = 0 :=
  (isZero_singularCochainComplex_of_isEmpty (TopCat.of A) n).eq_zero_of_tgt _

lemma relKern_eq_top_of_isEmpty (X : TopCat) (A : Set X) [IsEmpty (↥A)] (n : ℕ) :
    relKern ℤ X A n = ⊤ := by
  rw [relKern, restr_eq_zero_of_isEmpty X A n, ModuleCat.hom_zero, LinearMap.ker_zero]

lemma isIso_relIncl_of_isEmpty (X : TopCat) (A : Set X) [IsEmpty (↥A)] :
    IsIso (relIncl ℤ X A) :=
  isIso_relIncl_of_relKern_eq_top ℤ X A (fun n => relKern_eq_top_of_isEmpty X A n)

/-! ## `Good` at the maximal compact set `Set.univ` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The duality map of the `Good` framework at the whole space.**

From `Good N c Set.univ hU` one obtains bijectivity of the duality map at the maximal compact set
`K = Set.univ`: since `Set.univ` is cofinal among the compact subsets of `Set.univ`, the filtered
colimit degenerates to the module `H^n(M, M∖M)` itself. -/
theorem goodD_univ_bijective {M : TopCat} [CompactSpace M] [T2Space M] (n : ℕ)
    (c : (singularChains ℤ M).homology (n + n))
    (h : Good (n + n) c Set.univ isOpen_univ) :
    Function.Bijective (fun x : (relComplex ℤ (TopCat.of (Set.univ : Set M))
        (pdRelSub (Set.univ : Set M) Set.univ)).homology n =>
      goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
        isCompact_univ n n rfl x) := by
  -- the duality map is additive in the first variable (it is a cap product)
  have hsub : ∀ x₁ x₂ : (relComplex ℤ (TopCat.of (Set.univ : Set M))
      (pdRelSub (Set.univ : Set M) Set.univ)).homology n,
      goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
          isCompact_univ n n rfl (x₁ - x₂)
        = goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
            isCompact_univ n n rfl x₁
          - goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
            isCompact_univ n n rfl x₂ := by
    intro x₁ x₂
    simp only [goodD, map_sub, LinearMap.sub_apply]
  refine ⟨?_, ?_⟩
  · -- injectivity (via `Good.kill` at the maximal compact set)
    intro x₁ x₂ hx
    have h0 : goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
        isCompact_univ n n rfl (x₁ - x₂) = 0 := by
      rw [hsub x₁ x₂]
      have hxx : goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
          isCompact_univ n n rfl x₁
          = goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
            isCompact_univ n n rfl x₂ := hx
      rw [hxx, sub_self]
    obtain ⟨K', hUK', hK'U, hK'c, hkill⟩ :=
      Good.kill h n n rfl Set.univ (Set.subset_univ Set.univ) isCompact_univ (x₁ - x₂) h0
    have hK'eq : K' = Set.univ := Set.Subset.antisymm hK'U hUK'
    subst hK'eq
    rw [pdRelComplexEnlarge_self Set.univ hUK', HomologicalComplex.homologyMap_id] at hkill
    exact sub_eq_zero.mp (by simpa using hkill)
  · -- surjectivity (cofinality of `Set.univ` among the compact subsets of `Set.univ`)
    intro y
    obtain ⟨K, hKU, hKc, x, hx⟩ := Good.hit h n n rfl y
    refine ⟨(HomologicalComplex.homologyMap (pdRelComplexEnlarge Set.univ hKU) n) x, ?_⟩
    rw [← hx]
    exact pd_goodD_natural (n + n) c Set.univ isOpen_univ hKU hKU
      (Set.subset_univ Set.univ) hKc isCompact_univ n n rfl x

/-! ## The canonical homeomorphism `M ≅ {x // x ∈ Set.univ}` -/

/-- The canonical map `M ⟶ {x // x ∈ Set.univ}`. -/
def pdmd_univIncl (M : TopCat) : M ⟶ TopCat.of (Set.univ : Set M) :=
  TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩,
    Continuous.subtype_mk continuous_id (fun x => Set.mem_univ x)⟩

theorem pdmd_subtypeIncl_univ_univIncl (M : TopCat) :
    subtypeIncl M Set.univ ≫ pdmd_univIncl M = 𝟙 (TopCat.of (Set.univ : Set M)) := by
  apply TopCat.hom_ext
  ext y
  rfl

theorem pdmd_univIncl_subtypeIncl_univ (M : TopCat) :
    pdmd_univIncl M ≫ subtypeIncl M Set.univ = 𝟙 M := by
  apply TopCat.hom_ext
  ext x
  rfl

/-! ## The main theorem -/

/-- **The final degree reduction.**  If `Good (n+n) c Set.univ` holds for a class
`c ∈ H_{n+n}(M; ℤ)`, then the cap product `y ↦ y ⌢ c : H^n(M; ℤ) → H_n(M; ℤ)` is bijective. -/
theorem pd_middleDegree_of_good (n : ℕ) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + n))) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology (n + n))
    (h : Work.Cohomology.Good (n + n) c Set.univ isOpen_univ) :
    Function.Bijective (fun y : (Work.Cohomology.singularCochainComplex ℤ M).homology n =>
      (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) n n) y c) := by
  have hDU0 := goodD_univ_bijective n c h
  -- the canonical pair map `(Set.univ, Set.univ∖Set.univ) → (M, M∖Set.univ)`
  have h_eA : ∀ x ∈ pdRelSub (Set.univ : Set M) Set.univ,
      (subtypeIncl M Set.univ) x ∈ ((Set.univ : Set M)ᶜ) := fun x hx => hx
  have h_gA : ∀ y ∈ ((Set.univ : Set M)ᶜ),
      (pdmd_univIncl M) y ∈ pdRelSub (Set.univ : Set M) Set.univ := fun y hy => hy
  have heg : subtypeIncl M Set.univ ≫ pdmd_univIncl M = 𝟙 (TopCat.of (Set.univ : Set M)) :=
    pdmd_subtypeIncl_univ_univIncl M
  have hge : pdmd_univIncl M ≫ subtypeIncl M Set.univ = 𝟙 M := pdmd_univIncl_subtypeIncl_univ M
  -- the relevant maps, as local definitions
  let est : (singularChains ℤ (TopCat.of (Set.univ : Set M))).homology n
      → (singularChains ℤ M).homology n :=
    fun z => (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (Set.univ : Set M)) M
      (subtypeIncl M Set.univ)) n).hom z
  let gst : (singularChains ℤ M).homology n
      → (singularChains ℤ (TopCat.of (Set.univ : Set M))).homology n :=
    fun z => (HomologicalComplex.homologyMap (chainMap ℤ M (TopCat.of (Set.univ : Set M))
      (pdmd_univIncl M)) n).hom z
  let fMor := HomologicalComplex.homologyMap (relComplexMap ℤ
      (pdRelSub (Set.univ : Set M) Set.univ) ((Set.univ : Set M)ᶜ)
      (subtypeIncl M Set.univ) h_eA) n
  let incMor := HomologicalComplex.homologyMap (relIncl ℤ M ((Set.univ : Set M)ᶜ)) n
  let fst : (relComplex ℤ M ((Set.univ : Set M)ᶜ)).homology n
      → (relComplex ℤ (TopCat.of (Set.univ : Set M))
          (pdRelSub (Set.univ : Set M) Set.univ)).homology n := fun a => fMor.hom a
  let inc : (relComplex ℤ M ((Set.univ : Set M)ᶜ)).homology n
      → (singularCochainComplex ℤ M).homology n := fun a => incMor.hom a
  let DU : (relComplex ℤ (TopCat.of (Set.univ : Set M))
        (pdRelSub (Set.univ : Set M) Set.univ)).homology n
      → (singularChains ℤ (TopCat.of (Set.univ : Set M))).homology n :=
    fun x => goodD (n + n) c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
      isCompact_univ n n rfl x
  let DM : (relComplex ℤ M ((Set.univ : Set M)ᶜ)).homology n → (singularChains ℤ M).homology n :=
    fun a => relCapPair (TopCat.of M) ((Set.univ : Set M)ᶜ) n n a
      (relLocClass M (n + n) c Set.univ)
  let CP : (singularCochainComplex ℤ M).homology n → (singularChains ℤ M).homology n :=
    fun y => (capPair ℤ (TopCat.toSSet.obj M) n n) y c
  have hDU : Function.Bijective DU := hDU0
  -- the two pushforwards along the homeomorphism are mutually inverse
  have hid1 : (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (Set.univ : Set M)) M
        (subtypeIncl M Set.univ)) n)
        ≫ (HomologicalComplex.homologyMap (chainMap ℤ M (TopCat.of (Set.univ : Set M))
          (pdmd_univIncl M)) n) = 𝟙 ((singularChains ℤ (TopCat.of (Set.univ : Set M))).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← chainMap_comp' (TopCat.of (Set.univ : Set M)) M (TopCat.of (Set.univ : Set M))
        (subtypeIncl M Set.univ) (pdmd_univIncl M),
      heg, chainMap_id', HomologicalComplex.homologyMap_id]
  have hid2 : (HomologicalComplex.homologyMap (chainMap ℤ M (TopCat.of (Set.univ : Set M))
        (pdmd_univIncl M)) n)
        ≫ (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of (Set.univ : Set M)) M
          (subtypeIncl M Set.univ)) n) = 𝟙 ((singularChains ℤ M).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← chainMap_comp' M (TopCat.of (Set.univ : Set M)) M (pdmd_univIncl M) (subtypeIncl M Set.univ),
      hge, chainMap_id', HomologicalComplex.homologyMap_id]
  have hgf : ∀ z, gst (est z) = z := by
    intro z
    have hz := ConcreteCategory.congr_hom hid1 z
    simpa [est, gst] using hz
  have hfg : ∀ z, est (gst z) = z := by
    intro z
    have hz := ConcreteCategory.congr_hom hid2 z
    simpa [est, gst] using hz
  have hinj_est : Function.Injective est := by
    intro z₁ z₂ hz
    have h := congrArg gst hz
    rw [hgf z₁, hgf z₂] at h
    exact h
  -- the pullback along the homeomorphism of pairs is an isomorphism on relative cohomology
  haveI hfiso : IsIso fMor :=
    pdmd_relComplexMap_iso_of_isIso_pairs _ _ _ h_eA _ h_gA heg hge n
  -- the local fundamental class at `Set.univ` maps to the local class of `c`
  have heμ : (HomologicalComplex.homologyMap
        (relChainsMapOf (TopCat.of (Set.univ : Set M)) M (pdRelSub (Set.univ : Set M) Set.univ)
          ((Set.univ : Set M)ᶜ) (subtypeIncl M Set.univ)
          (relMapSub (pdRelSub (Set.univ : Set M) Set.univ) ((Set.univ : Set M)ᶜ)
            (subtypeIncl M Set.univ) h_eA)
          (relMapSub_spec (pdRelSub (Set.univ : Set M) Set.univ) ((Set.univ : Set M)ᶜ)
            (subtypeIncl M Set.univ) h_eA)) (n + n))
        (localFundClass (n + n) c Set.univ isOpen_univ Set.univ
          (Set.subset_univ Set.univ) isCompact_univ)
      = relLocClass M (n + n) c Set.univ := by
    rw [pdmd_relChainsMapOf_relMapSub_eq_relChainsMap M Set.univ ((Set.univ : Set M)ᶜ) h_eA]
    exact localFundClass_spec (n + n) c Set.univ isOpen_univ Set.univ
      (Set.subset_univ Set.univ) isCompact_univ
  -- naturality of the relative cap product under the homeomorphism of pairs
  have hnatur : ∀ a, est (DU (fst a)) = DM a := by
    intro a
    have hnn := Crux.relCapPair_natural (X₁ := TopCat.of (Set.univ : Set M)) (X₂ := M)
      (pdRelSub (Set.univ : Set M) Set.univ) ((Set.univ : Set M)ᶜ)
      (subtypeIncl M Set.univ) h_eA n n a
      (localFundClass (n + n) c Set.univ isOpen_univ Set.univ
        (Set.subset_univ Set.univ) isCompact_univ)
    rw [heμ] at hnn
    simpa only [est, DU, fst, DM, goodD] using hnn
  -- the pair map on relative cohomology is injective/surjective (it is an isomorphism)
  have hfi1 : ∀ a, (inv fMor).hom (fst a) = a := fun a => IsIso.hom_inv_id_apply fMor a
  have hfi2 : ∀ a, fst ((inv fMor).hom a) = a := fun a => IsIso.inv_hom_id_apply fMor a
  have hfinj : Function.Injective fst := fun a₁ a₂ h => by
    have hh := congrArg (fun z => (inv fMor).hom z) h
    rwa [hfi1 a₁, hfi1 a₂] at hh
  have hfsurj : Function.Surjective fst := fun b => ⟨(inv fMor).hom b, hfi2 b⟩
  -- bijectivity of the cap product with `relLocClass M (n+n) c Set.univ`
  have hDM : Function.Bijective DM := by
    refine ⟨?_, ?_⟩
    · intro a₁ a₂ h12
      have heq : est (DU (fst a₁)) = est (DU (fst a₂)) := by
        rw [hnatur a₁, hnatur a₂]
        exact h12
      have h1 : DU (fst a₁) = DU (fst a₂) := hinj_est heq
      exact hfinj (hDU.1 h1)
    · intro b
      obtain ⟨x, hx⟩ := hDU.2 (gst b)
      obtain ⟨a, ha⟩ := hfsurj x
      exact ⟨a, by rw [← hnatur a, ha, hx]; exact hfg b⟩
  -- the relative cap product with the local class is the absolute cap product
  have hAB2 : ∀ a, DM a = CP (inc a) := by
    intro a
    exact relCapPair_abs_eq_capPair M ((Set.univ : Set M)ᶜ) n n a c
  haveI hEmpty : IsEmpty (↥((Set.univ : Set M)ᶜ)) := ⟨fun x => x.2 trivial⟩
  haveI hRel : IsIso (relIncl ℤ M ((Set.univ : Set M)ᶜ)) :=
    isIso_relIncl_of_isEmpty M ((Set.univ : Set M)ᶜ)
  haveI hInclIso : IsIso incMor :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n)
      (relIncl ℤ M ((Set.univ : Set M)ᶜ))
  have hincsurj : Function.Surjective inc :=
    fun b => ⟨(inv incMor).hom b, IsIso.inv_hom_id_apply incMor b⟩
  have hCP : Function.Bijective CP := by
    refine ⟨?_, ?_⟩
    · intro y₁ y₂ hy
      obtain ⟨a₁, ha₁⟩ := hincsurj y₁
      obtain ⟨a₂, ha₂⟩ := hincsurj y₂
      have h1 : DM a₁ = DM a₂ := by
        rw [hAB2 a₁, hAB2 a₂, ha₁, ha₂]
        exact hy
      have h2 : a₁ = a₂ := hDM.1 h1
      rw [← ha₁, ← ha₂]
      exact congrArg inc h2
    · intro w
      obtain ⟨a, ha⟩ := hDM.2 w
      exact ⟨inc a, (hAB2 a).symm.trans ha⟩
  exact hCP

end

end Work.Cohomology
