import Mathlib
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Cohomology.Crux.relCapPair_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `Good` predicate: the elementwise form of Poincaré–Lefschetz duality

Let `M` be a topological space (later a closed manifold), `c ∈ H_N(M; ℤ)` a class, `W ⊆ M` an open
subset and `K ⊆ W` a compact subset.  Write

* `pdRelSub W K = {y : W | (y : M) ∉ K}` — the complement of `K` inside the subtype `W`;
* `localFundClass N c W K ∈ H_N(W, W∖K)` — **the local fundamental class of `c` at `K`**: the
  (unique, by excision) class whose image in `H_N(M, M∖K)` is the local class `relLocClass M N c K`
  of `c` (see `localFundClass_spec`);
* `goodD N c W K hkm : H^k(W, W∖K) → H_m(W)` for `k + m = N` — the map
  `x ↦ x ⌢ localFundClass N c W K`.

`Good N c W` is the *elementwise* form of "the duality map `D_W : H^k_c(W) → H_{N-k}(W)`,
`x ↦ x ⌢ μ_W`, is bijective", where `H^k_c(W) = colim_{K compact ⊆ W} H^k(W, W∖K)`:

* **(S)** (`Good.hit`) every `y ∈ H_m(W)` is `x ⌢ μ_K` for *some* compact `K ⊆ W` and some `x`
  — surjectivity of the map out of the filtered colimit;
* **(I)** (`Good.kill`) if `x ⌢ μ_K = 0` then `x` is killed by the transition map to a *larger*
  compact set — injectivity of the map out of the filtered colimit: this is exactly the description
  of equality in a filtered colimit of modules.

The point of the elementwise form is that no filtered-colimit machinery is needed: `Good W` is a
statement about the homology of the pairs `(W, W∖K)` alone.

## Contents

* `pdRelSub`, `localFundClass`, `localFundClass_spec`;
* `relChainsSubMap_eq_relCokerMap` — the two spellings of the enlargement map agree;
* `pdRelChainsEnlarge`, `pdRelComplexEnlarge` — the two enlargement maps;
* `pdRelChainsEnlarge_relChainsMap_comm` — the enlargement map commutes with the inclusions of
  pairs `(W, W∖K) → (M, M∖K)`;
* `pdRelChainsEnlarge_eq_relChainsMapOf` — the enlargement map is the map induced by the identity
  on the pairs;
* `goodD`, `Good`, `Good.hit`, `Good.kill`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-! ## The relative complement of a compact set inside an open set -/

/-- The complement of `K` inside the subtype `W`, viewed as a subset of `W`.  This is the subspace
that is quotiented out in the pair `(W, W∖K)`. -/
abbrev pdRelSub (W K : Set M) : Set W := {y | (y : M) ∈ Kᶜ}

@[simp] theorem pdRelSub_mem_iff (W K : Set M) (y : W) :
    y ∈ pdRelSub W K ↔ (y : M) ∉ K := Iff.rfl

/-- Monotonicity of `pdRelSub` in `K`: enlarging `K` shrinks `pdRelSub`. -/
theorem pdRelSub_mono {W : Set M} {K K' : Set M} (h : K ⊆ K') : pdRelSub W K' ⊆ pdRelSub W K :=
  fun y hy => fun hx => hy (h hx)

/-- The elementwise form of `pdRelSub_mono` for the identity map, as needed by `relMapSub`. -/
theorem pdRelSub_mono_id {W : Set M} {K K' : Set M} (h : K ⊆ K') :
    ∀ x ∈ pdRelSub W K', (𝟙 (TopCat.of W)) x ∈ pdRelSub W K :=
  fun x hx => pdRelSub_mono h hx

/-! ## The local fundamental class -/

section

variable [T2Space M]

/-- **The local fundamental class of `c` at the compact set `K` inside the open set `W`.**

This is the class in `H_N(W, W∖K)` corresponding, under the excision isomorphism
`H_N(W, W∖K) ≅ H_N(M, M∖K)`, to the local class `relLocClass M N c K` of `c`. -/
noncomputable def localFundClass (N : ℕ) (c : (singularChains ℤ M).homology N)
    (W : Set M) (hW : IsOpen W) (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K) :
    (relChains (TopCat.of W) (pdRelSub W K)).homology N :=
  letI : IsIso (HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N) :=
    excision_relChainsMap_isIso M W Kᶜ hW hKc.isClosed.isOpen_compl (by
      rw [Set.eq_univ_iff_forall]
      intro x
      by_cases h : x ∈ K
      · exact Or.inl (hKW h)
      · exact Or.inr h) N
  inv (HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N) (relLocClass M N c K)

/-- **The defining property of the local fundamental class**: its image under the inclusion of
pairs `(W, W∖K) → (M, M∖K)` is the local class `relLocClass M N c K` of `c`. -/
theorem localFundClass_spec (N : ℕ) (c : (singularChains ℤ M).homology N)
    (W : Set M) (hW : IsOpen W) (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K) :
    (HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N)
        (localFundClass N c W hW K hKW hKc) = relLocClass M N c K := by
  letI : IsIso (HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N) :=
    excision_relChainsMap_isIso M W Kᶜ hW hKc.isClosed.isOpen_compl (by
      rw [Set.eq_univ_iff_forall]
      intro x
      by_cases h : x ∈ K
      · exact Or.inl (hKW h)
      · exact Or.inr h) N
  exact IsIso.inv_hom_id_apply _ _

end

/-! ## The enlargement maps and their compatibility with excision -/

/-- The two spellings of the map of relative chain complexes induced by an inclusion of subsets
agree. -/
theorem relChainsSubMap_eq_relCokerMap (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    relChainsSubMap X A B h = relCokerMap X A B h := by
  apply (cancel_epi (cokernel.π (inclChains X A))).mp
  rw [relChainsSubMap_comp, relCokerMap_comp_π]

/-- **The enlargement map on relative chains**: the map `C_*(W, W∖K') → C_*(W, W∖K)` induced by
the inclusion of pairs `(W, W∖K) ⊆ (W, W∖K')` for `K ⊆ K'`. -/
def pdRelChainsEnlarge (W : Set M) {K K' : Set M} (h : K ⊆ K') :
    relChains (TopCat.of W) (pdRelSub W K') ⟶ relChains (TopCat.of W) (pdRelSub W K) :=
  relCokerMap (TopCat.of W) (pdRelSub W K') (pdRelSub W K) (pdRelSub_mono h)

/-- **The enlargement map on relative cochains**: the map `C^*(W, W∖K) → C^*(W, W∖K')` induced by
the contravariant functoriality of relative cochains in the pair, for `K ⊆ K'`. -/
def pdRelComplexEnlarge (W : Set M) {K K' : Set M} (h : K ⊆ K') :
    relComplex ℤ (TopCat.of W) (pdRelSub W K) ⟶ relComplex ℤ (TopCat.of W) (pdRelSub W K') :=
  relComplexMap ℤ (X₁ := TopCat.of W) (X₂ := TopCat.of W) (pdRelSub W K') (pdRelSub W K)
    (𝟙 (TopCat.of W)) (pdRelSub_mono h)

/-- **The compatibility of the enlargement map with excision**: the square

```
C_*(W, W∖K')  ⟶  C_*(W, W∖K)
     ↓                  ↓
C_*(M, M∖K')  ⟶  C_*(M, M∖K)
```

(the vertical maps are the inclusions of pairs, the horizontal ones the enlargement maps) commutes.
-/
theorem pdRelChainsEnlarge_relChainsMap_comm (W : Set M) {K K' : Set M} (h : K ⊆ K') :
    pdRelChainsEnlarge W h ≫ relChainsMap M W Kᶜ
      = relChainsMap M W K'ᶜ
        ≫ relCokerMap M K'ᶜ Kᶜ (fun x hx hxK => hx (h hxK)) := by
  rw [pdRelChainsEnlarge]
  apply (cancel_epi (cokernel.π (inclChains (TopCat.of W) (pdRelSub W K')))).mp
  conv_lhs => rw [← Category.assoc, relCokerMap_comp_π, cokernel_π_relChainsMap]
  conv_rhs => rw [← Category.assoc, cokernel_π_relChainsMap, Category.assoc, relCokerMap_comp_π]

/-- **The enlargement map is the map of relative chains induced by the identity of the pairs.** -/
theorem pdRelChainsEnlarge_eq_relChainsMapOf (W : Set M) {K K' : Set M} (h : K ⊆ K') :
    relChainsMapOf (TopCat.of W) (TopCat.of W) (pdRelSub W K') (pdRelSub W K) (𝟙 (TopCat.of W))
        (relMapSub (pdRelSub W K') (pdRelSub W K) (𝟙 (TopCat.of W))
          (pdRelSub_mono_id h))
        (relMapSub_spec (pdRelSub W K') (pdRelSub W K) (𝟙 (TopCat.of W))
          (pdRelSub_mono_id h))
      = pdRelChainsEnlarge W h := by
  rw [pdRelChainsEnlarge]
  apply (cancel_epi (cokernel.π (inclChains (TopCat.of W) (pdRelSub W K')))).mp
  rw [Crux.cruxCokernel_π_relChainsMapOf, relCokerMap_comp_π, chainMap_id', Category.id_comp]


/-! ## The inclusion of pairs `(V, V∖K) → (W, W∖K)` for `V ⊆ W`

These are the maps used to compare the duality maps of two open sets, one contained in the
other (see `pd_goodD_incl`). -/

/-- The inclusion `V ⟶ W` for `V ⊆ W ⊆ M`. -/
def pdIncl (W V : Set M) (hVW : V ⊆ W) : TopCat.of V ⟶ TopCat.of W :=
  TopCat.ofHom ⟨fun y => ⟨(y : M), hVW y.2⟩,
    Continuous.subtype_mk (f := fun y : V => (y : M)) continuous_subtype_val (fun y => hVW y.2)⟩

/-- The inclusion `V∖K ⟶ W∖K` for `V ⊆ W ⊆ M`. -/
def pdInclSub (W V : Set M) (hVW : V ⊆ W) (K : Set M) :
    TopCat.of (pdRelSub V K) ⟶ TopCat.of (pdRelSub W K) :=
  TopCat.ofHom ⟨fun y => ⟨⟨(y.1 : M), hVW y.1.2⟩, y.2⟩,
    Continuous.subtype_mk
      (f := fun y : pdRelSub V K => (⟨((y.1 : V) : M), hVW y.1.2⟩ : W))
      (Continuous.subtype_mk (f := fun y : pdRelSub V K => ((y.1 : V) : M))
        (continuous_subtype_val.comp continuous_subtype_val) (fun y => hVW y.1.2))
      (fun y => y.2)⟩

/-- The compatibility needed to build the map of relative chain complexes of the two pairs. -/
theorem pdIncl_compat (W V : Set M) (hVW : V ⊆ W) (K : Set M) :
    subtypeIncl (TopCat.of V) (pdRelSub V K) ≫ pdIncl W V hVW
      = pdInclSub W V hVW K ≫ subtypeIncl (TopCat.of W) (pdRelSub W K) := by
  ext y; rfl

/-! ## The duality map `D_W^K` and the `Good` predicate -/

section

variable [T2Space M]

/-- **The duality map with compact support at `K`**:
`D_W^K : H^k(W, W∖K) → H_m(W)`, `x ↦ x ⌢ μ_K`, where `k + m = N` and `μ_K` is the local
fundamental class of `c` at `K`. -/
noncomputable def goodD (N : ℕ) (c : (singularChains ℤ M).homology N)
    (W : Set M) (hW : IsOpen W) (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K)
    (k m : ℕ) (hkm : k + m = N)
    (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    (singularChains ℤ (TopCat.of W)).homology m :=
  relCapPair (TopCat.of W) (pdRelSub W K) k m x (hkm ▸ localFundClass N c W hW K hKW hKc)

/-- **The `Good` predicate.**  `Good N c W` (for `W ⊆ M` open) is the elementwise form of the
statement that the duality map `H^k_c(W) → H_{N-k}(W)`, `x ↦ x ⌢ μ_W`, is bijective. -/
def Good (N : ℕ) (c : (singularChains ℤ M).homology N) (W : Set M) (hW : IsOpen W) : Prop :=
  ∀ (k m : ℕ) (hkm : k + m = N),
    (∀ y : (singularChains ℤ (TopCat.of W)).homology m,
      ∃ (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K)
        (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k),
        goodD N c W hW K hKW hKc k m hkm x = y) ∧
    (∀ (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K)
       (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k),
       goodD N c W hW K hKW hKc k m hkm x = 0 →
       ∃ (K' : Set M) (hKK' : K ⊆ K') (hK'W : K' ⊆ W) (hK'c : IsCompact K'),
         (HomologicalComplex.homologyMap (pdRelComplexEnlarge W hKK') k) x = 0)

/-- The surjectivity clause of `Good`. -/
theorem Good.hit {N : ℕ} {c : (singularChains ℤ M).homology N} {W : Set M} {hW : IsOpen W}
    (h : Good N c W hW) (k m : ℕ) (hkm : k + m = N)
    (y : (singularChains ℤ (TopCat.of W)).homology m) :
    ∃ (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K)
      (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k),
      goodD N c W hW K hKW hKc k m hkm x = y :=
  (h k m hkm).1 y

/-- The injectivity clause of `Good`. -/
theorem Good.kill {N : ℕ} {c : (singularChains ℤ M).homology N} {W : Set M} {hW : IsOpen W}
    (h : Good N c W hW) (k m : ℕ) (hkm : k + m = N)
    (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K)
    (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k)
    (hx : goodD N c W hW K hKW hKc k m hkm x = 0) :
    ∃ (K' : Set M) (hKK' : K ⊆ K') (hK'W : K' ⊆ W) (hK'c : IsCompact K'),
      (HomologicalComplex.homologyMap (pdRelComplexEnlarge W hKK') k) x = 0 :=
  (h k m hkm).2 K hKW hKc x hx

end

end

end Work.Cohomology
