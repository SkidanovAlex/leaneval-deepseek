import Mathlib
import Submission.Work.Cohomology.pd_crux_weak

/-!
# The weak crux identity, support form

This file proves `Work.Cohomology.pd_crux_weak2`, a variant of `pd_crux_weak` in which the
hypothesis that `α₁ + α₂ + α₃` is a *cycle* is replaced by the weaker requirement that its
boundary be *supported in* `(K ∪ L)ᶜ` (i.e. that it vanish upon restriction to `Kᶜ` and to `Lᶜ`).

Concretely, with `d = Σ_i (-1)^i δ_i`, the statement is again

  `d (α₁ ⌢ φ) - (-1)^(k+1) • (α₂ ⌢ δφA) ∈ range d`,

with the explicit witness `- d (α₂ ⌢ φA)`.

The proof follows `pd_crux_weak` verbatim once one replaces the identity `d α₁ = -(d α₂ + d α₃)`
by the two support facts

* `cap φA mj (d α₁) + cap φA mj (d α₂) = 0`, obtained from
  `d (α₁ + α₂ + α₃) = d α₁ + d α₂ + d α₃ ∈ range (inclChains M (K ∪ L)ᶜ) ⊆ range (inclChains M Kᶜ)`
  and the vanishing of `cap φA mj (d α₃)`;
* the vanishing of `cap φB mj (d α₁)`.

## Main statements

* `cap_eq_zero_of_supported` — the cap product of a cochain vanishing on `A` with a chain
  supported in a subset `B ⊆ A` vanishes;
* `pd_crux_weak2` — the goal.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## An elementary vanishing lemma -/

/-- **The cap product with a relative cochain kills chains supported in a smaller set.**  If `φ`
vanishes on the `k`-chains supported in `A` (that is, `φ ∈ C^k(M,A)`) and `x` is a `(k+m)`-chain
supported in `B ⊆ A`, then `cap φ m x = 0`. -/
lemma cap_eq_zero_of_supported {M : TopCat} {A B : Set M} (hBA : B ⊆ A) {k m : ℕ}
    (φ : Cochain ℤ (TopCat.toSSet.obj M) k) (hφ : φ ∈ relKern ℤ M A k)
    {x : (singularChains ℤ M).X (k + m)}
    (hx : x ∈ LinearMap.range ((inclChains M B).f (k + m)).hom) :
    cap ℤ (TopCat.toSSet.obj M) φ m x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have hz := cap_inclChains_eq_zero M A φ hφ m ((inclChainsSub M B A hBA).f (k + m) y)
  have hfin : (ModuleCat.Hom.hom ((inclChains M B).f (k + m))) y
      = (ModuleCat.Hom.hom ((inclChains M A).f (k + m)))
          ((ModuleCat.Hom.hom ((inclChainsSub M B A hBA).f (k + m))) y) := by
    rw [← inclChainsSub_comp M B A hBA, HomologicalComplex.comp_f]
    rfl
  rw [hfin]
  exact hz

/-! ## The crux identity, support form -/

theorem pd_crux_weak2 {M : TopCat} {K L : Set M} {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ M).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj M) k)
    (hφA : φA ∈ relKern ℤ M Kᶜ k) (hφB : φB ∈ relKern ℤ M Lᶜ k)
    (hφ : φ ∈ relKern ℤ M Kᶜ k)
    (hlift : φ = φA - φB)
    (hL : ∃ e', (inclChains M Lᶜ).f (k + mj) e'
      = (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)
    (hK : ∃ f', (inclChains M Kᶜ).f (k + mj) f'
      = (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃)
    (hd : ∃ g', (inclChains M ((K ∪ L)ᶜ)).f (k + mj) g'
      = (singularChains ℤ M).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃))
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂))
      ∈ LinearMap.range (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)) := by
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  obtain ⟨g', hg'⟩ := hd
  -- `(K ∪ L)ᶜ ⊆ Kᶜ`
  have hsub : ((K ∪ L)ᶜ : Set M) ⊆ Kᶜ :=
    Set.compl_subset_compl.mpr Set.subset_union_left
  -- `φB` kills the boundary of `α₁` (supported in `Lᶜ`)
  have hzeroB : cap ℤ (TopCat.toSSet.obj M) φB mj
      ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero M Lᶜ φB hφB mj e'
  -- `φA` kills the boundary of `α₃` (supported in `Kᶜ`)
  have hzeroA3 : cap ℤ (TopCat.toSSet.obj M) φA mj
      ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero M Kᶜ φA hφA mj f'
  -- `φA` kills the boundary of the total chain (supported in `(K ∪ L)ᶜ ⊆ Kᶜ`)
  have hzeroAtot : cap ℤ (TopCat.toSSet.obj M) φA mj
      ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)) = 0 := by
    rw [← hg']
    exact cap_eq_zero_of_supported hsub φA hφA ⟨g', rfl⟩
  -- the boundary of the total chain splits
  have hdsum : (singularChains ℤ M).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
      = (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁
        + (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂
        + (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [map_add, map_add]
  -- hence `cap φA mj (dα₂) = - cap φA mj (dα₁)`
  have hA2 : cap ℤ (TopCat.toSSet.obj M) φA mj
        ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂)
      = - cap ℤ (TopCat.toSSet.obj M) φA mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁) := by
    have hsum : cap ℤ (TopCat.toSSet.obj M) φA mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)
        + cap ℤ (TopCat.toSSet.obj M) φA mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂) = 0 := by
      have h := hzeroAtot
      rw [hdsum] at h
      rw [map_add, map_add, hzeroA3, add_zero] at h
      exact h
    exact eq_neg_of_add_eq_zero_right hsum
  -- the cap of `d α₁` with `φ` is the cap of `d α₂` with `φA`, up to sign
  have hP : cap ℤ (TopCat.toSSet.obj M) φ mj
        ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj M) φA mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂) := by
    rw [hlift, cap_sub_apply, hzeroB, sub_zero, hA2, neg_neg]
  -- the boundary formula for the cocycle `φ` applied to `α₁`
  have hA : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      = (-1 : ℤ) ^ k • cap ℤ (TopCat.toSSet.obj M) φ mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁) := by
    have h := cap_d ℤ (TopCat.toSSet.obj M) (n := k) (m := mj) φ α₁
    rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj M)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj M) φ mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)))
  -- the boundary formula for `φA` applied to `α₂`
  have hB : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ k • (cap ℤ (TopCat.toSSet.obj M) φA mj
            ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj M) (n := k) (m := mj) φA α₂
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj M)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj M) φA mj
            ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)))
  -- the arithmetic combination
  have key : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂))
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂)) := by
    rw [hA, hP, hB]
    rw [zsmul_neg]
    rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
    abel
  rw [LinearMap.mem_range]
  exact ⟨- cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂, by rw [map_neg, ← key]⟩

end

end Work.Cohomology
