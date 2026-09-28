import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_hatcher_W

/-!
# The local fundamental class as the class of a relative cycle

Given an open set `W ⊆ M` (`M` Hausdorff), a compact `K ⊆ W`, a cycle `αW ∈ Z_N(W)` whose class in
`H_N(M)` is `c`, the image `π αW` of `αW` in the relative chain complex `C_*(W, W∖K)` is a relative
cycle whose underlying chain is the image of the underlying chain of `αW`, and whose class in
`H_N(W, W∖K)` is the local fundamental class `localFundClass N c W K` of `c` at `K`.

The mathematical content is `relCycle_homologyMap_eq_relLocClass` (from `pd_hatcher_W`), applied
with `ξ = iCycles αW`, `w = cyclesMap (inclChains M W) αW` and `j = 0`: the chain `iCycles αW` maps
to `iCycles (cyclesMap (inclChains M W) αW)` in `C_*(M)`, and this cycle represents `c` by
hypothesis.  The resulting statement that the image of the class under excision is `relLocClass`
is then turned around using that the excision map is an isomorphism and the defining property
`localFundClass_spec`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

theorem pd_localFundClass_of_cycle {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N} {W : Set M} (hW : IsOpen W)
    {K : Set M} (hKW : K ⊆ W) (hKc : IsCompact K)
    (αW : (Work.Cohomology.singularChains ℤ (TopCat.of W)).cycles N)
    (hc : HomologicalComplex.homologyMap (Work.Cohomology.inclChains M W) N
        (HomologicalComplex.homologyπ (Work.Cohomology.singularChains ℤ (TopCat.of W)) N αW)
        = c) :
    ∃ γ : (Work.Cohomology.relChains (TopCat.of W) (Work.Cohomology.pdRelSub W K)).cycles N,
      (Work.Cohomology.relChains (TopCat.of W) (Work.Cohomology.pdRelSub W K)).iCycles N γ
        = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of W)
            (Work.Cohomology.pdRelSub W K))).f N).hom
          ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles N αW) ∧
      (Work.Cohomology.relChains (TopCat.of W) (Work.Cohomology.pdRelSub W K)).homologyπ N γ
        = Work.Cohomology.localFundClass N c W hW K hKW hKc := by
  classical
  -- the relative cycle `π αW`
  let πW := CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of W) (Work.Cohomology.pdRelSub W K))
  let γ : (Work.Cohomology.relChains (TopCat.of W) (Work.Cohomology.pdRelSub W K)).cycles N :=
    HomologicalComplex.cyclesMap πW N αW
  -- its underlying chain is the image of the underlying chain of `αW`
  have hγi : (Work.Cohomology.relChains (TopCat.of W) (Work.Cohomology.pdRelSub W K)).iCycles N γ
      = ((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of W)
          (Work.Cohomology.pdRelSub W K))).f N).hom
        ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles N αW) := by
    dsimp only [γ, πW]
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
    rfl
  refine ⟨γ, hγi, ?_⟩
  -- the excision map `H_N(W, W∖K) → H_N(M, M∖K)` is an isomorphism
  have hiso : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M W Kᶜ) N) :=
    Work.Cohomology.excision_relChainsMap_isIso M W Kᶜ hW hKc.isClosed.isOpen_compl (by
      rw [Set.eq_univ_iff_forall]; intro x
      by_cases h : x ∈ K
      · exact Or.inl (hKW h)
      · exact Or.inr h) N
  haveI := hiso
  -- the inclusion of `W` into `M` carries the class of `αW` to `c`
  have hw : HomologicalComplex.homologyπ (Work.Cohomology.singularChains ℤ M) N
      (HomologicalComplex.cyclesMap (Work.Cohomology.inclChains M W) N αW) = c := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
    exact hc
  -- the underlying chain of `αW` maps to the underlying chain of its image cycle
  have hξ : (Work.Cohomology.inclChains M W).f N
        ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles N αW)
      = (Work.Cohomology.singularChains ℤ M).iCycles N
          (HomologicalComplex.cyclesMap (Work.Cohomology.inclChains M W) N αW) - 0 := by
    rw [sub_zero, ← ModuleCat.comp_apply, ← HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
  -- the excision image of the class of `γ` is the local class of `c`
  have hcl := Work.Cohomology.relCycle_homologyMap_eq_relLocClass (M := M) c γ hγi hw hξ (by simp)
  have hspec := Work.Cohomology.localFundClass_spec N c W hW K hKW hKc
  calc (Work.Cohomology.relChains (TopCat.of W) (Work.Cohomology.pdRelSub W K)).homologyπ N γ
      = inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M W Kᶜ) N)
          (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M W Kᶜ) N
            ((Work.Cohomology.relChains (TopCat.of W)
              (Work.Cohomology.pdRelSub W K)).homologyπ N γ)) :=
          (IsIso.hom_inv_id_apply _ _).symm
    _ = inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M W Kᶜ) N)
          (Work.Cohomology.relLocClass M N c K) := by rw [hcl]
    _ = inv (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M W Kᶜ) N)
          (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M W Kᶜ) N
            (Work.Cohomology.localFundClass N c W hW K hKW hKc)) := by rw [hspec]
    _ = Work.Cohomology.localFundClass N c W hW K hKW hKc := IsIso.hom_inv_id_apply _ _

end Work.Cohomology
