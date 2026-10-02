import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.TripleSetup
import Submission.Work.Orient.Boundary.tripleConnectingMap_surjective_of_isRelFundClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary-orientation convention

`Work.Orient.BoundaryOrientationConvention` (Hatcher 3.43, second half): the connecting map
`hPairδ : H_{n+1}(W, ∂W) → H_n(∂W)` of the pair `(W, ∂W)` sends a relative fundamental class to a
fundamental class of the boundary.

## The route

Write `B := ∂W`, `A := H_{n+1}(W,B)` and, for `y ∈ B`,

`Δ_y : A ⟶ H_n(B, B∖{y})`

for the connecting map of the **triple** `B∖{y} ⊆ B ⊆ W` (`Work.Cohomology.tripleShort`, whose
connecting map is `(relChains_triple_shortExact W (B∖{y}) B ·).δ`).

1. **The local class of `hPairδ W B n w` at `y` is the image of `Δ_y w`.**  The local group of the
   space `↥B` at `y` has two models — `coker (C_*(B∖{y}) → C_*(B))` (the model used by the
   connecting map of the triple) and `coker (C_*(↥B∖{y}) → C_*(↥B))` (the model used by
   `Work.Orient.locClass`) — canonically isomorphic because `B∖{y}` and `↥B∖{y}` are canonically
   homeomorphic.  Ingredient 1 (`hPairδ_comp_localization_eq_tripleδ`) identifies the composite of
   `hPairδ` with the localisation at `y` with `Δ_y`; `diffCokerMap` compares the two models and
   `diffCokerMap_isIso` says the comparison is an isomorphism.

2. **`span{Δ_y w} = ⊤`.**  This is proved *without* any connectivity or uniqueness input.  Take a
   coordinate half-ball `K` around `y` and let `P := K ∩ W°` be its interior part (so
   `H_{n+1}(W, W∖P)` is the "localisation group over the half-ball").  Then:

   * `ρ : A → H_{n+1}(W, W∖P)` has `span{ρ w} = ⊤`: for an interior point `x ∈ P` the localisation
     `H_{n+1}(W, W∖P) → H_{n+1}(W, W∖{x})` is injective and `ℓ_x w` generates
     `H_{n+1}(W, W∖{x})` (the hypothesis `IsRelFundClass`);
   * `δ' : H_{n+1}(W, W∖P) → H_n(B', A)` is onto (`triple_δ_surjective_of_isZero`);
   * the excision map `e : H_n(B, B∖{y}) → H_n(B', A)` is injective
     (`tripleConnecting_input₁`) and commutes with `ρ`, `δ'` (`tripleMap_delta_naturality`).

   The abstract linear-algebra step `span_eq_top_of_surjective_injective` then gives
   `span{Δ_y w} = ⊤`.

3. From 1. and 2., and the surjectivity of `homologyMap (diffCokerMap ·) n` (from
   `diffCokerMap_isIso`), the local class of `hPairδ W B n w` at `y` generates the local group.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-! ## 0. The two models of `B ∖ {y}` and the comparison of their local groups -/

/-- The canonical homeomorphism between the two subtypes of `B ∖ {y}`, the one inside `W`
(`↥(B ∖ {y})`) and the one inside `↥B` (`↥{z : ↥B | z ≠ y}`).  These are the two models of the
local group of `B` at `y`; `diffCokerMap` below compares them. -/
def diffHomeo (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B) :
    ↥(B \ {y}) ≃ₜ ↥{z : ↥B | z ≠ ⟨y, hy⟩} where
  toFun z := ⟨⟨z.1, z.2.1⟩, by
    intro h
    exact z.2.2 (Subtype.ext_iff.mp h)⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, by
    intro h
    exact z.2 (Subtype.ext h)⟩⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The inclusion `↥(B ∖ {y}) → ↥B`, named so that its `Set.diff`-membership proof is never
re-elaborated (which is what goes wrong when `Work.Cohomology.inclChainsSub` is mentioned
directly: its `h`-argument is re-checked at `implicit` transparency). -/
def diffIncl (W : TopCat.{0}) (B : Set W) (y : W) :
    TopCat.of ↥(B \ {y}) ⟶ TopCat.of ↥B :=
  TopCat.ofHom ⟨fun z => ⟨z.1, z.2.1⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

/-- `diffHomeo` followed by the inclusion of `{z : ↥B | z ≠ y}` into `↥B` is the named inclusion
`diffIncl`. -/
theorem diffHomeo_comp_subtypeIncl (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B) :
    TopCat.ofHom ⟨(diffHomeo W B y hy).toFun, (diffHomeo W B y hy).continuous_toFun⟩
      ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩}
    = diffIncl W B y := by
  ext z
  rfl

/-- **The chain-level comparison of the two presentations.**  Composing the chains of
`↥(B ∖ {y})` with `diffHomeo` and then including into the chains of `↥B` is the named inclusion
`diffIncl`. -/
theorem chainMap_diffHomeo_comp_inclChains (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B) :
    Work.Cohomology.chainMap ℤ (TopCat.of ↥(B \ {y})) (TopCat.of ↥{z : ↥B | z ≠ ⟨y, hy⟩})
        (TopCat.ofHom ⟨(diffHomeo W B y hy).toFun, (diffHomeo W B y hy).continuous_toFun⟩)
      ≫ Work.Cohomology.inclChains (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩}
    = Work.Cohomology.chainMap ℤ (TopCat.of ↥(B \ {y})) (TopCat.of ↥B) (diffIncl W B y) := by
  rw [Work.Cohomology.inclChains, Work.Cohomology.chainMap_compPD,
    diffHomeo_comp_subtypeIncl W B y hy]

/-- **The bridge to `inclChainsSub`.**  The chain map used by `Work.Cohomology.inclChainsSub` is
the chain map of the named inclusion `diffIncl`.  (This is the only place where the
`Set.diff`-membership proof of `inclChainsSub` is ever unfolded; everything downstream mentions
`diffIncl`.) -/
theorem inclChainsSub_eq_chainMap_diffIncl (W : TopCat.{0}) (B : Set W) (y : W)
    (h : B \ {y} ⊆ B) :
    Work.Cohomology.inclChainsSub W (B \ {y}) B h
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(B \ {y})) (TopCat.of ↥B) (diffIncl W B y) := by
  rw [Work.Cohomology.inclChainsSub]
  congr 1

/-- **The comparison of the two models of the local group of `B` at `y`**, as a map of cokernels
along the chain-level comparison `chainMap_diffHomeo_comp_inclChains`. -/
noncomputable def diffCokerMap (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B)
    (hB : B \ {y} ⊆ B) :
    CategoryTheory.Limits.cokernel (Work.Cohomology.inclChainsSub W (B \ {y}) B hB)
      ⟶ CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains (TopCat.of ↥B)
          {z : ↥B | z ≠ ⟨y, hy⟩}) :=
  CategoryTheory.Limits.cokernel.map (Work.Cohomology.inclChainsSub W (B \ {y}) B hB)
    (Work.Cohomology.inclChains (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩})
    (Work.Cohomology.chainMap ℤ (TopCat.of ↥(B \ {y})) (TopCat.of ↥{z : ↥B | z ≠ ⟨y, hy⟩})
      (TopCat.ofHom ⟨(diffHomeo W B y hy).toFun, (diffHomeo W B y hy).continuous_toFun⟩))
    (𝟙 _)
    (by rw [CategoryTheory.Category.comp_id, inclChainsSub_eq_chainMap_diffIncl W B y hB,
      ← chainMap_diffHomeo_comp_inclChains W B y hy])

/-- The chain-level comparison in the opposite direction, composed with the inclusion of `B ∖ {y}`
into `↥B`, is the inclusion of `{z : ↥B | z ≠ y}`. -/
theorem chainMap_diffHomeoSymm_comp_inclChainsSub (W : TopCat.{0}) (B : Set W) (y : W)
    (hy : y ∈ B) (hB : B \ {y} ⊆ B) :
    Work.Cohomology.chainMap ℤ (TopCat.of ↥{z : ↥B | z ≠ ⟨y, hy⟩}) (TopCat.of ↥(B \ {y}))
        (TopCat.ofHom ⟨(diffHomeo W B y hy).symm.toFun,
          (diffHomeo W B y hy).symm.continuous_toFun⟩)
      ≫ Work.Cohomology.inclChainsSub W (B \ {y}) B hB
    = Work.Cohomology.inclChains (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩} := by
  have hcomp : (TopCat.ofHom ⟨(diffHomeo W B y hy).symm.toFun,
        (diffHomeo W B y hy).symm.continuous_toFun⟩ :
        TopCat.of ↥{z : ↥B | z ≠ ⟨y, hy⟩} ⟶ TopCat.of ↥(B \ {y})) ≫ diffIncl W B y
      = Work.Cohomology.subtypeIncl (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩} := by
    ext z
    rfl
  rw [inclChainsSub_eq_chainMap_diffIncl W B y hB, Work.Cohomology.inclChains,
    Work.Cohomology.chainMap_compPD, hcomp]

/-- The map of cokernels in the opposite direction, i.e. the inverse of `diffCokerMap`. -/
noncomputable def diffCokerMapInv (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B)
    (hB : B \ {y} ⊆ B) :
    CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains (TopCat.of ↥B)
        {z : ↥B | z ≠ ⟨y, hy⟩})
      ⟶ CategoryTheory.Limits.cokernel (Work.Cohomology.inclChainsSub W (B \ {y}) B hB) :=
  CategoryTheory.Limits.cokernel.map
    (Work.Cohomology.inclChains (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩})
    (Work.Cohomology.inclChainsSub W (B \ {y}) B hB)
    (Work.Cohomology.chainMap ℤ (TopCat.of ↥{z : ↥B | z ≠ ⟨y, hy⟩}) (TopCat.of ↥(B \ {y}))
      (TopCat.ofHom ⟨(diffHomeo W B y hy).symm.toFun,
        (diffHomeo W B y hy).symm.continuous_toFun⟩))
    (𝟙 _)
    (by rw [CategoryTheory.Category.comp_id]
        exact (chainMap_diffHomeoSymm_comp_inclChainsSub W B y hy hB).symm)

/-- **The defining property of `diffCokerMap`**: it intertwines the two projections. -/
theorem diffCokerMap_π (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B) (hB : B \ {y} ⊆ B) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChainsSub W (B \ {y}) B hB)
      ≫ diffCokerMap W B y hy hB
    = 𝟙 _ ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥B)
        {z : ↥B | z ≠ ⟨y, hy⟩}) := by
  rw [diffCokerMap]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

theorem diffCokerMap_hom_inv (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B)
    (hB : B \ {y} ⊆ B) :
    diffCokerMap W B y hy hB ≫ diffCokerMapInv W B y hy hB = 𝟙 _ := by
  apply (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChainsSub W (B \ {y}) B hB))).mp
  rw [← CategoryTheory.Category.assoc, diffCokerMap_π, CategoryTheory.Category.id_comp,
    diffCokerMapInv, Work.Cohomology.cokernel_π_map, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

theorem diffCokerMap_inv_hom (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B)
    (hB : B \ {y} ⊆ B) :
    diffCokerMapInv W B y hy hB ≫ diffCokerMap W B y hy hB = 𝟙 _ := by
  apply (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of ↥B) {z : ↥B | z ≠ ⟨y, hy⟩}))).mp
  rw [← CategoryTheory.Category.assoc, diffCokerMapInv, Work.Cohomology.cokernel_π_map,
    CategoryTheory.Category.id_comp, diffCokerMap_π, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

/-- **`diffCokerMap` is an isomorphism**: the two models of the local group of `B` at `y` agree. -/
theorem diffCokerMap_isIso (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B)
    (hB : B \ {y} ⊆ B) : IsIso (diffCokerMap W B y hy hB) :=
  ⟨diffCokerMapInv W B y hy hB, diffCokerMap_hom_inv W B y hy hB,
    diffCokerMap_inv_hom W B y hy hB⟩

/-- **The transport of the local class.**  The two projections of the chains of `↥B` onto the
local group at `y` — the one through `C_*(B∖{y})` (used by
`hPairδ_comp_localization_eq_tripleδ`) and the one through `C_*(↥B ∖ {y})` (used by
`Work.Orient.locClass`) — agree up to the comparison `diffCokerMap`. -/
theorem diffCokerMap_localClass (W : TopCat.{0}) (B : Set W) (y : W) (hy : y ∈ B)
    (hB : B \ {y} ⊆ B) (n : ℕ)
    (x : (Work.Cohomology.singularChains ℤ (TopCat.of ↥B)).homology n) :
    (HomologicalComplex.homologyMap (diffCokerMap W B y hy hB) n)
        ((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChainsSub W (B \ {y}) B hB)) n) x)
      = (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥B)
            {z : ↥B | z ≠ ⟨y, hy⟩})) n) x := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, diffCokerMap_π]
  rw [CategoryTheory.Category.id_comp]

/-! ## 1. Ingredient 1: the connecting map of the pair through the localisation

The local class of `hPairδ W ∂W n w` at a boundary point `y` is the composite of `hPairδ W ∂W n`
with the localisation `C_*(∂W) → C_*(∂W, ∂W∖{y})`.  The next theorem identifies this composite
with the connecting map of the **triple** `∂W∖{y} ⊆ ∂W ⊆ W`. -/
theorem hPairδ_comp_localization_eq_tripleδ (n : ℕ) (W : TopCat.{0}) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W)
    (hB : bdrySetW n W \ {y} ⊆ bdrySetW n W) :
    CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.hPairδ W (bdrySetW n W) n)
        (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChainsSub W
            (bdrySetW n W \ {y}) (bdrySetW n W) hB)) n)
      = (Work.Cohomology.relChains_triple_shortExact W
            (bdrySetW n W \ {y}) (bdrySetW n W) hB).δ (n + 1) n
          (by simp [ComplexShape.down]) := by
  classical
  let B : Set W := bdrySetW n W
  have hB' : B \ {y} ⊆ B := hB
  have hc₁ :
      CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChainsSub W (B \ {y}) B hB'))
          (CategoryTheory.Limits.cokernel.map (Work.Cohomology.inclChainsSub W (B \ {y}) B hB')
            (Work.Cohomology.inclChains W (B \ {y})) (𝟙 _) (Work.Cohomology.inclChains W B)
            (by rw [CategoryTheory.Category.id_comp]
                exact Work.Cohomology.inclChainsSub_comp W (B \ {y}) B hB'))
        = CategoryTheory.CategoryStruct.comp (Work.Cohomology.inclChains W B)
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains W (B \ {y}))) :=
    Work.Cohomology.cokernel_π_map _ _ _ _ _
  have hc₂ :
      CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains W (B \ {y})))
          (CategoryTheory.Limits.cokernel.desc (Work.Cohomology.inclChains W (B \ {y}))
            (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains W B))
            (by rw [← Work.Cohomology.inclChainsSub_comp W (B \ {y}) B hB',
              CategoryTheory.Category.assoc, CategoryTheory.Limits.cokernel.condition]
                exact CategoryTheory.Limits.comp_zero))
        = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains W B)) (𝟙 _) := by
    rw [CategoryTheory.Limits.cokernel.π_desc, CategoryTheory.Category.comp_id]
  have hcomm₁ : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChainsSub W (B \ {y}) B hB'))
        (Work.Cohomology.tripleShort W (B \ {y}) B hB').f
      = CategoryTheory.CategoryStruct.comp (Work.Cohomology.hPairShort W B).f
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains W (B \ {y}))) := hc₁
  have hcomm₂ : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains W (B \ {y})))
        (Work.Cohomology.tripleShort W (B \ {y}) B hB').g
      = CategoryTheory.CategoryStruct.comp (Work.Cohomology.hPairShort W B).g (𝟙 _) := hc₂
  let φ : Work.Cohomology.hPairShort W B ⟶ Work.Cohomology.tripleShort W (B \ {y}) B hB' :=
    CategoryTheory.ShortComplex.homMk _ _ (𝟙 _) hcomm₁ hcomm₂
  have key := HomologicalComplex.HomologySequence.δ_naturality φ
    (Work.Cohomology.hPairShort_shortExact W B)
    (Work.Cohomology.relChains_triple_shortExact W (B \ {y}) B hB')
    (n + 1) n (by simp [ComplexShape.down])
  rw [← CategoryTheory.Category.id_comp ((Work.Cohomology.relChains_triple_shortExact W
    (B \ {y}) B hB').δ (n + 1) n (by simp [ComplexShape.down]))]
  rw [← HomologicalComplex.homologyMap_id
    (K := (Work.Cohomology.tripleShort W (B \ {y}) B hB').X₃) (i := n+1)]
  exact key

/-! ## 2. `span{ρ w}` and `span{Δ_y w}` -/

/-- **A generator maps to a generator under a surjection.** -/
theorem span_eq_top_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {v : M}
    (hv : Submodule.span ℤ ({v} : Set M) = ⊤) :
    Submodule.span ℤ ({f v} : Set N) = ⊤ := by
  have hmap : Submodule.map f (Submodule.span ℤ ({v} : Set M))
      = Submodule.span ℤ ({f v} : Set N) := by
    rw [Submodule.map_span]
    simp
  rw [← hmap, hv]
  refine Submodule.eq_top_iff'.mpr (fun y => ?_)
  obtain ⟨w, rfl⟩ := hf y
  exact Submodule.mem_map_of_mem Submodule.mem_top

/-- **The abstract step.**  If `τ₁ ∘ δ₁ = δ₂ ∘ τ₃` (a commuting square of linear maps),
`τ₁` injective, `δ₂` onto, and `τ₃ w` generates its group, then `δ₁ w` generates its group. -/
theorem span_eq_top_of_surjective_injective {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module ℤ M₁] [AddCommGroup M₂] [Module ℤ M₂]
    [AddCommGroup N₁] [Module ℤ N₁] [AddCommGroup N₂] [Module ℤ N₂]
    (δ₁ : M₁ →ₗ[ℤ] N₁) (δ₂ : M₂ →ₗ[ℤ] N₂) (τ₃ : M₁ →ₗ[ℤ] M₂) (τ₁ : N₁ →ₗ[ℤ] N₂)
    (w : M₁) (hsq : ∀ a : M₁, τ₁ (δ₁ a) = δ₂ (τ₃ a))
    (hinj : Function.Injective τ₁) (hsurj : Function.Surjective δ₂)
    (hspan : Submodule.span ℤ ({τ₃ w} : Set M₂) = ⊤) :
    Submodule.span ℤ ({δ₁ w} : Set N₁) = ⊤ := by
  have h₂ : Submodule.span ℤ ({δ₂ (τ₃ w)} : Set N₂) = ⊤ :=
    span_eq_top_of_surjective δ₂ hsurj hspan
  have hτ : Submodule.map τ₁ (Submodule.span ℤ ({δ₁ w} : Set N₁)) = ⊤ := by
    rw [Submodule.map_span, Set.image_singleton, hsq w]
    exact h₂
  refine Submodule.eq_top_iff'.mpr (fun c => ?_)
  have hc : τ₁ c ∈ Submodule.map τ₁ (Submodule.span ℤ ({δ₁ w} : Set N₁)) := by
    rw [hτ]; exact Submodule.mem_top
  obtain ⟨s, hs, hsc⟩ := Submodule.mem_map.mp hc
  exact (hinj hsc).symm ▸ hs

/-- **The localisation over the interior part `P = K ∩ W°` of a coordinate half-ball at a boundary
point generates**: for `x ∈ P` the map `H_{n+1}(W, W∖P) → H_{n+1}(W, W∖{x})` is injective and the
local class of `w` at `x` generates, so the localisation of `w` over `P` generates. -/
theorem span_relCokerMap_eq_top (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ bdrySetW n W) (r : ℝ) (hr : 0 < r)
    (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (w : (Work.Cohomology.relChains W (bdrySetW n W)).homology (n + 1))
    (hw : Work.Orient.IsRelFundClass W (n + 1) (bdrySetW n W) w) :
    Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W (bdrySetW n W) (bigB n W y r)
          (bdrySetW_sub_bigB n W y r)) (n + 1))) w)} :
      Set ((Work.Cohomology.relChains W (bigB n W y r)).homology (n + 1))) = ⊤ := by
  classical
  obtain ⟨x, hxK, hxbdry⟩ := exists_mem_halfBallPiece_and_notMem_boundary n W y hy r hr hgood
  have hxnotB : x ∉ bdrySetW n W := hxbdry
  have hxnotB' : x ∉ bigB n W y r := fun h => h ⟨hxK, hxbdry⟩
  have hinc : bigB n W y r ⊆ (({x} : Set W))ᶜ := fun _ hz hzx => hxnotB' (hzx ▸ hz)
  have hsing : ({x} : Set W) ⊆ halfBallK n W y r ∩ (bdrySetW n W)ᶜ :=
    Set.singleton_subset_iff.mpr ⟨hxK, hxbdry⟩
  have hLid : Work.Orient.resRelH W (n + 1) hsing
      = (HomologicalComplex.homologyMap
          (Work.Orient.relChainsIncl W (A := bigB n W y r) (B := (({x} : Set W))ᶜ) hinc)
          (n + 1)).hom := by
    have hmap : Work.Cohomology.relCokerMap W (bigB n W y r) (({x} : Set W))ᶜ
          (Set.compl_subset_compl.mpr hsing)
        = Work.Orient.relChainsIncl W (A := bigB n W y r) (B := (({x} : Set W))ᶜ) hinc :=
      (relChainsIncl_eq_relCokerMap W hinc).symm
    unfold Work.Orient.resRelH Work.ThomBordism.RelHmap
    rw [hmap]
  set ρm : Work.Cohomology.relChains W (bdrySetW n W) ⟶
      Work.Cohomology.relChains W (bigB n W y r) :=
    Work.Cohomology.relCokerMap W (bdrySetW n W) (bigB n W y r)
      (bdrySetW_sub_bigB n W y r) with hρm
  have hcomp : Work.Orient.relPunct W (bdrySetW n W) x hxnotB
      = ρm ≫ Work.Orient.relChainsIncl W (A := bigB n W y r) (B := (({x} : Set W))ᶜ) hinc := by
    rw [hρm, relPunct_eq_relChainsIncl]
    rw [← relChainsIncl_comp (X := W) (bdrySetW_sub_bigB n W y r) hinc]
    rw [relChainsIncl_eq_relCokerMap (X := W) (bdrySetW_sub_bigB n W y r)]
  have hLρ : (Work.Orient.resRelH W (n + 1) hsing).comp
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1)))
      = ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W (bdrySetW n W) x hxnotB) (n + 1)) := by
    rw [hLid, hcomp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  let Hloc : (Work.Cohomology.relChains W (bdrySetW n W)).homology (n + 1) →ₗ[ℤ]
      Work.Orient.RelH W (n + 1) {x} :=
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.relPunct W (bdrySetW n W) x hxnotB) (n + 1))
  have hHloc : ∀ a, Hloc a = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Orient.relPunct W (bdrySetW n W) x hxnotB) (n + 1))) a := fun _ => rfl
  have hLcomp : ∀ a, (Work.Orient.resRelH W (n + 1) hsing)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) a) = Hloc a := by
    intro a
    rw [hHloc]
    exact congrArg (fun (f : _ →ₗ[ℤ] _) => f a) hLρ
  have hLinj : Function.Injective (Work.Orient.resRelH W (n + 1) hsing) :=
    Work.Orient.Boundary.injective_localisation_of_halfBallInterior n W y hy r hr hgood x
      ⟨hxK, hxbdry⟩
  have hmap : Submodule.map (Work.Orient.resRelH W (n + 1) hsing)
      (Submodule.span ℤ ({(ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) w} :
        Set _)) = ⊤ := by
    rw [Submodule.map_span, Set.image_singleton, hLcomp w, hHloc, hw x hxnotB]
  refine Submodule.eq_top_iff'.mpr (fun v => ?_)
  have hv : (Work.Orient.resRelH W (n + 1) hsing) v
      ∈ Submodule.map (Work.Orient.resRelH W (n + 1) hsing)
        (Submodule.span ℤ ({(ModuleCat.Hom.hom (HomologicalComplex.homologyMap ρm (n + 1))) w} :
          Set _)) := by
    rw [hmap]; exact Submodule.mem_top
  obtain ⟨s, hs, hsv⟩ := Submodule.mem_map.mp hv
  exact (hLinj hsv).symm ▸ hs

/-- **`span{Δ_y w} = ⊤`** for `w` a relative fundamental class.  Assembled from the two geometric
inputs (`tripleConnecting_input₁`, `triple_δ_surjective_of_isZero`), the naturality square
`tripleMap_delta_naturality`, and `span_relCokerMap_eq_top`. -/
theorem span_delta_eq_top (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (w : (Work.Cohomology.relChains W (bdrySetW n W)).homology (n + 1))
    (hw : Work.Orient.IsRelFundClass W (n + 1) (bdrySetW n W) w)
    (y : W) (hy : y ∈ bdrySetW n W) :
    Submodule.span ℤ ({(((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y)
        (bdrySetW n W) (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
        (by simp [ComplexShape.down])) w)} : Set _) = ⊤ := by
  classical
  obtain ⟨r, hr, hgood, -⟩ :=
    Work.Orient.Boundary.exists_halfBall_subset n (W := W) (U := Set.univ) isOpen_univ
      (Set.mem_univ y)
  have hspanρ : Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W (bdrySetW n W) (bigB n W y r)
          (bdrySetW_sub_bigB n W y r)) (n + 1))) w)} : Set _) = ⊤ :=
    span_relCokerMap_eq_top n W y hy r hr hgood w hw
  have hτ₃eq : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleMap W
        (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
        (bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap W (bdrySetW n W) (bigB n W y r)
          (bdrySetW_sub_bigB n W y r)) (n + 1))) := rfl
  have hspanτ : Submodule.span ℤ ({((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (tripleMap W (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
          (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)).τ₃ (n + 1))) w)} :
      Set _) = ⊤ := by
    rw [hτ₃eq]
    exact hspanρ
  have hsq : ∀ a : (Work.Cohomology.relChains W (bdrySetW n W)).homology (n + 1),
      (HomologicalComplex.homologyMap (tripleMap W (bdryMinus_sub_bdrySetW n W y)
          (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
          (bdrySetW_sub_bigB n W y r)).τ₁ n)
        (((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y) (bdrySetW n W)
          (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n (by simp [ComplexShape.down])) a)
      = ((Work.Cohomology.relChains_triple_shortExact W (bigA n W y r) (bigB n W y r)
            (bigA_sub_bigB n W y r)).δ (n + 1) n (by simp [ComplexShape.down]))
        ((HomologicalComplex.homologyMap (tripleMap W (bdryMinus_sub_bdrySetW n W y)
          (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
          (bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)) a) := by
    intro a
    have hnat := tripleMap_delta_naturality W (bdryMinus_sub_bdrySetW n W y)
      (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r) n
    have h := congrArg (fun (φ : (Work.Cohomology.tripleShort W (bdryMinus n W y) (bdrySetW n W)
          (bdryMinus_sub_bdrySetW n W y)).X₃.homology (n + 1) ⟶
        (Work.Cohomology.tripleShort W (bigA n W y r) (bigB n W y r)
          (bigA_sub_bigB n W y r)).X₁.homology n) => φ a) hnat
    simpa only [ModuleCat.comp_apply] using h
  exact span_eq_top_of_surjective_injective
    (ModuleCat.Hom.hom ((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y)
      (bdrySetW n W) (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n (by simp [ComplexShape.down])))
    (ModuleCat.Hom.hom ((Work.Cohomology.relChains_triple_shortExact W (bigA n W y r)
      (bigB n W y r) (bigA_sub_bigB n W y r)).δ (n + 1) n (by simp [ComplexShape.down])))
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleMap W
      (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
      (bdrySetW_sub_bigB n W y r)).τ₃ (n + 1)))
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (tripleMap W
      (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
      (bdrySetW_sub_bigB n W y r)).τ₁ n))
    w hsq (tripleConnecting_input₁ n W y hy r hr hgood)
    (triple_δ_surjective_of_isZero n W y hy r hr hgood) hspanτ

/-! ## 3. The boundary-orientation convention -/

theorem BoundaryOrientation : Work.Orient.BoundaryOrientationConvention := by
  intro n W _ _ _ _ w hw
  intro x
  obtain ⟨y, hy⟩ := x
  have hyB : y ∈ bdrySetW n W := hy
  have hspan : Submodule.span ℤ ({((ModuleCat.Hom.hom
      ((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y)
        (bdrySetW n W) (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
        (by simp [ComplexShape.down]))) w)} : Set _) = ⊤ :=
    span_delta_eq_top n W w hw y hyB
  have h1 : (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bdrySetW n W)
          (bdryMinus_sub_bdrySetW n W y))) n)
        (Work.Cohomology.hPairδ W (bdrySetW n W) n w)
      = ((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y)
          (bdrySetW n W) (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])) w := by
    rw [← ModuleCat.comp_apply,
      hPairδ_comp_localization_eq_tripleδ n W y (bdryMinus_sub_bdrySetW n W y)]
    congr 1 <;> try rfl <;> exact Subsingleton.elim _ _
  have h2 := diffCokerMap_localClass W (bdrySetW n W) y hyB
    (bdryMinus_sub_bdrySetW n W y) n (Work.Cohomology.hPairδ W (bdrySetW n W) n w)
  rw [h1] at h2
  have hloc : locClass (TopCat.of (bdrySetW n W)) n
        (Work.Cohomology.hPairδ W (bdrySetW n W) n w) ⟨y, hyB⟩
      = (HomologicalComplex.homologyMap
          (diffCokerMap W (bdrySetW n W) y hyB (bdryMinus_sub_bdrySetW n W y)) n)
        (((Work.Cohomology.relChains_triple_shortExact W (bdryMinus n W y)
          (bdrySetW n W) (bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])) w) := by
    rw [h2]
    rfl
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (diffCokerMap W (bdrySetW n W) y hyB (bdryMinus_sub_bdrySetW n W y)) n) := by
    intro v
    refine ⟨(HomologicalComplex.homologyMap (diffCokerMapInv W (bdrySetW n W) y hyB
      (bdryMinus_sub_bdrySetW n W y)) n) v, ?_⟩
    have hcomp : HomologicalComplex.homologyMap (diffCokerMapInv W (bdrySetW n W) y hyB
          (bdryMinus_sub_bdrySetW n W y)) n
        ≫ HomologicalComplex.homologyMap (diffCokerMap W (bdrySetW n W) y hyB
          (bdryMinus_sub_bdrySetW n W y)) n = 𝟙 _ := by
      rw [← HomologicalComplex.homologyMap_comp, diffCokerMap_inv_hom,
        HomologicalComplex.homologyMap_id]
    rw [← ModuleCat.comp_apply, hcomp, ModuleCat.id_apply]
  rw [hloc]
  exact span_eq_top_of_surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (diffCokerMap W (bdrySetW n W) y hyB (bdryMinus_sub_bdrySetW n W y)) n)) hsurj hspan

end

end Work.Orient.Boundary
