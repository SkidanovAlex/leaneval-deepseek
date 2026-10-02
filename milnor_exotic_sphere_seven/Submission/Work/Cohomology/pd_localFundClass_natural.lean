import Mathlib
import Submission.Work.Cohomology.pd_good

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the local fundamental class

`localFundClass N c W K ∈ H_N(W, W∖K)` is the class corresponding, under the excision isomorphism
`H_N(W, W∖K) ≅ H_N(M, M∖K)`, to the local class `relLocClass M N c K` of `c`.  This file proves
that it is natural in `K`: for `K ⊆ K'` the enlargement map
`pdRelChainsEnlarge W h : C_*(W, W∖K') → C_*(W, W∖K)` carries the class at `K'` to the class at `K`.

The proof is the naturality square `pdRelChainsEnlarge_relChainsMap_comm` together with the
functoriality `relLocClass_restrict` of the local classes and the defining property
`localFundClass_spec` of the local fundamental class (both sides are the excision inverse of the
same local class).
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

open HomologicalComplex

noncomputable section


theorem pd_localFundClass_natural {M : TopCat} [T2Space M] (N : ℕ)
    (c : (singularChains ℤ M).homology N)
    (W : Set M) (hW : IsOpen W) {K K' : Set M} (h : K ⊆ K')
    (hKW : K ⊆ W) (hK'W : K' ⊆ W) (hKc : IsCompact K) (hK'c : IsCompact K') :
    (HomologicalComplex.homologyMap (pdRelChainsEnlarge W h) N)
        (localFundClass N c W hW K' hK'W hK'c)
      = localFundClass N c W hW K hKW hKc := by
  -- The excision maps are isomorphisms: the pairs `(W, W∖K)` and the covers `{W, Kᶜ}` of `M`
  -- satisfy the hypothesis of excision since `K ⊆ W`.
  have hcovK : (W : Set M) ∪ Kᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKW hx)
    · exact Or.inr hx
  have hcovK' : (W : Set M) ∪ K'ᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K'
    · exact Or.inl (hK'W hx)
    · exact Or.inr hx
  -- Abbreviations for the two excision isomorphisms and the enlargement map on homology.
  let A : (relChains (TopCat.of W) (pdRelSub W K)).homology N ⟶ (relChains M Kᶜ).homology N :=
    HomologicalComplex.homologyMap (relChainsMap M W Kᶜ) N
  let A' : (relChains (TopCat.of W) (pdRelSub W K')).homology N ⟶ (relChains M K'ᶜ).homology N :=
    HomologicalComplex.homologyMap (relChainsMap M W K'ᶜ) N
  let B : (relChains M K'ᶜ).homology N ⟶ (relChains M Kᶜ).homology N :=
    HomologicalComplex.homologyMap (relCokerMap M K'ᶜ Kᶜ (fun x hx hxK => hx (h hxK))) N
  letI hA : IsIso A := excision_relChainsMap_isIso M W Kᶜ hW hKc.isClosed.isOpen_compl hcovK N
  letI hA' : IsIso A' := excision_relChainsMap_isIso M W K'ᶜ hW hK'c.isClosed.isOpen_compl hcovK' N
  -- The naturality square `pdRelChainsEnlarge_relChainsMap_comm` on homology.
  have key2 : HomologicalComplex.homologyMap (pdRelChainsEnlarge W h) N ≫ A = A' ≫ B :=
    (HomologicalComplex.homologyMap_comp (pdRelChainsEnlarge W h) (relChainsMap M W Kᶜ) N).symm.trans
      ((congrArg (fun φ => HomologicalComplex.homologyMap φ N)
        (pdRelChainsEnlarge_relChainsMap_comm W h)).trans
        (HomologicalComplex.homologyMap_comp (relChainsMap M W K'ᶜ)
          (relCokerMap M K'ᶜ Kᶜ (fun x hx hxK => hx (h hxK))) N))
  -- Elementwise form of the square.
  have keyfun : ∀ z : (relChains (TopCat.of W) (pdRelSub W K')).homology N,
      A ((HomologicalComplex.homologyMap (pdRelChainsEnlarge W h) N) z) = B (A' z) := by
    intro z
    have hz := CategoryTheory.ConcreteCategory.congr_hom key2 z
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hz
    exact hz
  -- Both sides are the excision inverse of the same local class.
  calc
    (HomologicalComplex.homologyMap (pdRelChainsEnlarge W h) N)
        (localFundClass N c W hW K' hK'W hK'c)
        = inv A (A ((HomologicalComplex.homologyMap (pdRelChainsEnlarge W h) N)
              (localFundClass N c W hW K' hK'W hK'c))) :=
            (IsIso.hom_inv_id_apply A _).symm
    _ = inv A (B (A' (localFundClass N c W hW K' hK'W hK'c))) := by rw [keyfun]
    _ = inv A (B (relLocClass M N c K')) := by rw [localFundClass_spec]
    _ = inv A (relLocClass M N c K) := by erw [relLocClass_restrict M N c h]
    _ = inv A (A (localFundClass N c W hW K hKW hKc)) := by rw [← localFundClass_spec]
    _ = localFundClass N c W hW K hKW hKc := IsIso.hom_inv_id_apply A _

end

end Work.Cohomology
