import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_localFundClass_natural
import Submission.Work.Cohomology.localHomology

/-!
# Naturality of the duality map `goodD` in the open set

`goodD N c W hW K hKW hKc k m hkm : H^k(W, W∖K) → H_m(W)` is the cap product with the local
fundamental class `localFundClass N c W hW K hKW hKc ∈ H_N(W, W∖K)` of `c` at `K`
(`Work.Cohomology.goodD`).

For open sets `V ⊆ W` and a compact `K ⊆ V`, the pair `(V, V∖K)` maps into the pair
`(W, W∖K)` (pullback `relComplexMap` on relative cochains, pushforward `relChainsMapOf` on
relative chains, pushforward `chainMap` on absolute chains).  The two duality maps are compatible
with these maps:

`goodD_K^V (x|_(V,V∖K)) ⌢ μ_K^V` pushed into `W` equals `x ⌢ μ_K^W`,

i.e. the compactly supported duality map is natural in the open set.  This is the statement that
`goodD` is compatible with the restriction maps of the filtered system
`H^k_c(W) = colim_{K compact ⊆ W} H^k(W, W∖K)` *and* with the dependence of `W` on the ambient
space.

The proof has three ingredients:

* `pdRelChainsMapOf_incl_comp` — the composite of the pair maps `(V,V∖K) → (W,W∖K) → (M,M∖K)` is
  the pair map `(V,V∖K) → (M,M∖K)` (functoriality of `relChainsMapOf`, proved on the cokernels);
* `pd_localFundClass_incl` — naturality of the local fundamental class in the open set: the
  pushforward of `μ_K^V` is `μ_K^W` (both are the excision inverse of the same local class
  `relLocClass M N c K`);
* `Crux.relCapPair_natural` — naturality of the relative cap product under a map of pairs.

## Contents

* `pdRelChainsMapOf_incl_comp`
* `pd_localFundClass_incl`
* `pd_goodD_incl_aux`, `pd_goodD_incl`
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Functoriality of the pair map `(V, V∖K) → (W, W∖K) → (M, M∖K)` -/

/-- **Functoriality of the pair maps for an inclusion of open sets.**  For `V ⊆ W ⊆ M` and
`K ⊆ M`, the pair map `(V, V∖K) → (W, W∖K)` followed by the inclusion of pairs
`(W, W∖K) → (M, M∖K)` is the inclusion of pairs `(V, V∖K) → (M, M∖K)`.

The proof cancels the projection `C_*(V) → C_*(V, V∖K)`, where both composites are computed
with `Crux.cruxCokernel_π_relChainsMapOf` and `cokernel_π_relChainsMap`. -/
theorem pdRelChainsMapOf_incl_comp {M : TopCat} {W V : Set M} (hVW : V ⊆ W) (K : Set M)
    (h : ∀ y ∈ pdRelSub V K, (pdIncl W V hVW) y ∈ pdRelSub W K) :
    (relChainsMapOf (TopCat.of V) (TopCat.of W) (pdRelSub V K) (pdRelSub W K)
        (pdIncl W V hVW) (relMapSub (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h)
        (relMapSub_spec (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h))
      ≫ relChainsMap M W Kᶜ = relChainsMap M V Kᶜ := by
  apply (cancel_epi (cokernel.π (inclChains (TopCat.of V) (pdRelSub V K)))).1
  rw [← Category.assoc, Crux.cruxCokernel_π_relChainsMapOf, Category.assoc,
      cokernel_π_relChainsMap M W Kᶜ, ← Category.assoc, chainMap_compPD,
      cokernel_π_relChainsMap M V Kᶜ,
      show pdIncl W V hVW ≫ subtypeIncl M W = subtypeIncl M V from by ext x; rfl]

/-! ## Naturality of the local fundamental class in the open set -/

/-- **Naturality of the local fundamental class in the open set.**  For open `V ⊆ W` and a compact
`K ⊆ V`, the pushforward of the local fundamental class `μ_K^V ∈ H_N(V, V∖K)` along the pair map
`(V, V∖K) → (W, W∖K)` induced by the inclusion `V ⊆ W` is the local fundamental class
`μ_K^W ∈ H_N(W, W∖K)`.

Indeed both classes are the excision inverse of the same local class `relLocClass M N c K`: the
excision isomorphisms `H_N(V, V∖K) → H_N(M, M∖K)` and `H_N(W, W∖K) → H_N(M, M∖K)` are related by
the functoriality `pdRelChainsMapOf_incl_comp` of the pair maps, so the pushforward of
`μ_K^V = A_V^{-1}(relLocClass)` is `A_W^{-1}(A_W(P A_V^{-1}(relLocClass)))
= A_W^{-1}(relLocClass) = μ_K^W`. -/
theorem pd_localFundClass_incl {M : TopCat} [T2Space M] (N : ℕ)
    (c : (singularChains ℤ M).homology N)
    {W V : Set M} (hVW : V ⊆ W) (hW : IsOpen W) (hV : IsOpen V)
    {K : Set M} (hKV : K ⊆ V) (hKW : K ⊆ W) (hKc : IsCompact K)
    (h : ∀ y ∈ pdRelSub V K, (pdIncl W V hVW) y ∈ pdRelSub W K) :
    (HomologicalComplex.homologyMap
      (relChainsMapOf (TopCat.of V) (TopCat.of W) (pdRelSub V K) (pdRelSub W K)
        (pdIncl W V hVW) (relMapSub (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h)
        (relMapSub_spec (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h)) N)
      (localFundClass N c V hV K hKV hKc) = localFundClass N c W hW K hKW hKc := by
  have hcovV : (V : Set M) ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKV hx)
    · exact Or.inr hx
  have hcovW : (W : Set M) ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKW hx)
    · exact Or.inr hx
  -- The two excision isomorphisms and the map induced on homology by the pair map.
  let A_V : (relChains (TopCat.of V) (pdRelSub V K)).homology N ⟶ (relChains M Kᶜ).homology N :=
    HomologicalComplex.homologyMap (relChainsMap M V Kᶜ) N
  let A_W : (relChains (TopCat.of W) (pdRelSub W K)).homology N ⟶ (relChains M Kᶜ).homology N :=
    HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N
  let P : (relChains (TopCat.of V) (pdRelSub V K)).homology N
      ⟶ (relChains (TopCat.of W) (pdRelSub W K)).homology N :=
    HomologicalComplex.homologyMap (relChainsMapOf (TopCat.of V) (TopCat.of W)
      (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW)
      (relMapSub (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h)
      (relMapSub_spec (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h)) N
  have hAV : IsIso A_V := excision_relChainsMap_isIso M V Kᶜ hV hKc.isClosed.isOpen_compl hcovV N
  have hAW : IsIso A_W := excision_relChainsMap_isIso M W Kᶜ hW hKc.isClosed.isOpen_compl hcovW N
  -- Functoriality of the pair maps, on homology.
  have hsq : P ≫ A_W = A_V := by
    have hcomp := HomologicalComplex.homologyMap_comp
      (relChainsMapOf (TopCat.of V) (TopCat.of W) (pdRelSub V K) (pdRelSub W K)
        (pdIncl W V hVW) (relMapSub (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h)
        (relMapSub_spec (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h))
      (relChainsMap M W Kᶜ) N
    rw [pdRelChainsMapOf_incl_comp hVW K h] at hcomp
    exact hcomp.symm
  have hA : ∀ z : (relChains (TopCat.of V) (pdRelSub V K)).homology N, A_W (P z) = A_V z := by
    intro z
    have hz := CategoryTheory.ConcreteCategory.congr_hom hsq z
    rwa [CategoryTheory.comp_apply] at hz
  -- Both classes are the excision inverse of the same local class.
  have hspecV := localFundClass_spec N c V hV K hKV hKc
  have hspecW := localFundClass_spec N c W hW K hKW hKc
  change P (localFundClass N c V hV K hKV hKc) = localFundClass N c W hW K hKW hKc
  calc P (localFundClass N c V hV K hKV hKc)
      = inv A_W (A_W (P (localFundClass N c V hV K hKV hKc))) :=
          (IsIso.hom_inv_id_apply A_W _).symm
    _ = inv A_W (A_V (localFundClass N c V hV K hKV hKc)) := by rw [hA]
    _ = inv A_W (relLocClass M N c K) := by rw [hspecV]
    _ = inv A_W (A_W (localFundClass N c W hW K hKW hKc)) := by rw [← hspecW]
    _ = localFundClass N c W hW K hKW hKc := IsIso.hom_inv_id_apply A_W _

/-! ## Naturality of `goodD` in the open set -/

/-- **Naturality of the duality map in the open set**, for an arbitrary map of pairs on the
subspaces `V∖K → W∖K`.  The statement of `pd_goodD_incl` is the case of the canonical map
`(fun y hy => hy)`; the general form is what makes the proof (which has to manipulate the pair
map `relChainsMapOf`) robust under definitional unfolding. -/
theorem pd_goodD_incl_aux {M : TopCat} [T2Space M] {W V : Set M} (hVW : V ⊆ W)
    (hW : IsOpen W) (hV : IsOpen V)
    {K : Set M} (hKV : K ⊆ V) (hKW : K ⊆ W) (hKc : IsCompact K)
    (N : ℕ) (c : (singularChains ℤ M).homology N)
    (k m : ℕ) (hkm : k + m = N)
    (h : ∀ y ∈ pdRelSub V K, (pdIncl W V hVW) y ∈ pdRelSub W K)
    (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    (HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of V) (TopCat.of W) (pdIncl W V hVW)) m)
      (goodD N c V hV K hKV hKc k m hkm
        ((HomologicalComplex.homologyMap
          (relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := TopCat.of W) (pdRelSub V K) (pdRelSub W K)
            (pdIncl W V hVW) h) k) x))
      = goodD N c W hW K hKW hKc k m hkm x := by
  -- Remove the degree bookkeeping `hkm`: both sides live in `H_{k+m}`.
  subst hkm
  -- Unfold the duality maps into cap products with the local fundamental classes.
  simp only [goodD]
  -- Naturality of the relative cap product for the pair map `(V, V∖K) → (W, W∖K)`.
  have hnat := Crux.relCapPair_natural (X₁ := TopCat.of V) (X₂ := TopCat.of W)
      (pdRelSub V K) (pdRelSub W K) (pdIncl W V hVW) h k m x
      (localFundClass (k + m) c V hV K hKV hKc)
  -- The class at `V` pushes forward to the class at `W`.
  rw [pd_localFundClass_incl (k + m) c hVW hW hV hKV hKW hKc h] at hnat
  simpa using hnat

/-- **Naturality of the duality map `goodD` in the open set.**  For open sets `V ⊆ W`, a compact
`K ⊆ V` and `x ∈ H^k(W, W∖K)`, pulling `x` back to `(V, V∖K)`, capping with the local
fundamental class of `c` at `K` in `V` and pushing the result forward to `W` is the same as
capping `x` with the local fundamental class of `c` at `K` in `W`.

This says that the duality maps `D_W^K = (_ ⌢ μ_K^W)` of the filtered system defining compactly
supported cohomology are compatible with the inclusions `V ⊆ W`. -/
theorem pd_goodD_incl {M : TopCat} [T2Space M] {W V : Set M} (hVW : V ⊆ W)
    (hW : IsOpen W) (hV : IsOpen V)
    {K : Set M} (hKV : K ⊆ V) (hKW : K ⊆ W) (hKc : IsCompact K)
    (N : ℕ) (c : (singularChains ℤ M).homology N)
    (k m : ℕ) (hkm : k + m = N)
    (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    (HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of V) (TopCat.of W) (pdIncl W V hVW)) m)
      (goodD N c V hV K hKV hKc k m hkm
        ((HomologicalComplex.homologyMap
          (relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := TopCat.of W) (pdRelSub V K) (pdRelSub W K)
            (pdIncl W V hVW) (fun y hy => hy)) k) x))
      = goodD N c W hW K hKW hKc k m hkm x := by
  exact pd_goodD_incl_aux hVW hW hV hKV hKW hKc N c k m hkm (fun y hy => hy) x

end

end Work.Cohomology
