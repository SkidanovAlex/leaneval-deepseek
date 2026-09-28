import Mathlib
import Submission.Work.Cohomology.pd_union_aux
import Submission.Work.Cohomology.relCapH
import Submission.Work.Cohomology.relChainsProjective

/-!
# The duality map on cycle representatives

`goodD N c W hW K hKW hKc k m hkm : H^k(W, W∖K) → H_m(W)` is the cap product with the local
fundamental class `μ ∈ H_N(W, W∖K)` (`Work.Cohomology.goodD`).  This file records its value on
homology classes coming from explicit cocycle and cycle representatives:

if `z` is a relative cocycle of degree `k`, `γ` a relative cycle of degree `k + m` whose class is
`μ`, and `ξ` a chain of `W` lifting `γ`, then

  `goodD ... (homologyπ z) = homologyπ (cap (z's cochain) (m) ξ)`.

The computation is `relCapPair_apply` (the pairing is computed on representatives by
`relCapPairZ`), `relCapPairZ_iCycles` (the underlying chain of `relCapPairZ` is `relCapHalf`),
`relChains_cokernelIso_canon_apply` (the canonical lift) and `relCapHalf_apply_incl` (the relative
cap product on a representing chain is the absolute one).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The relative cap product on cycle representatives.** -/
theorem relCapPairZ_iCycles_apply {X : TopCat} (A : Set X) {n m : ℕ}
    (z : (relComplex ℤ X A).cycles n) (γ : (relChains X A).cycles (n + m))
    {ξ : (singularChains ℤ X).X (n + m)}
    (hξ : (relChains X A).iCycles (n + m) γ
      = ((cokernel.π (inclChains X A)).f (n + m)).hom ξ) :
    (singularChains ℤ X).iCycles m (relCapPairZ X A n m z γ)
      = cap ℤ (TopCat.toSSet.obj X) (((relComplex ℤ X A).iCycles n).hom z).1 m ξ := by
  rw [relCapPairZ_iCycles, hξ, relChains_cokernelIso_canon_apply]
  exact relCapHalf_apply_incl X A (((relComplex ℤ X A).iCycles n).hom z) ξ

/-- **The duality map on cycle representatives.** -/
theorem goodD_homologyπ {M : TopCat} [T2Space M] {N : ℕ} (c : (singularChains ℤ M).homology N)
    (W : Set M) (hW : IsOpen W) (K : Set M) (hKW : K ⊆ W) (hKc : IsCompact K)
    (k m : ℕ) (hkm : k + m = N)
    (z : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).cycles k)
    (γ : (relChains (TopCat.of W) (pdRelSub W K)).cycles (k + m))
    (hγ : (relChains (TopCat.of W) (pdRelSub W K)).homologyπ (k + m) γ
      = hkm ▸ localFundClass N c W hW K hKW hKc)
    (ξ : (singularChains ℤ (TopCat.of W)).X (k + m))
    (hξ : (relChains (TopCat.of W) (pdRelSub W K)).iCycles (k + m) γ
      = ((cokernel.π (inclChains (TopCat.of W) (pdRelSub W K))).f (k + m)).hom ξ) :
    goodD N c W hW K hKW hKc k m hkm
        ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homologyπ k z)
      = (singularChains ℤ (TopCat.of W)).homologyπ m
          (relCapPairZ (TopCat.of W) (pdRelSub W K) k m z γ) := by
  rw [goodD, ← hγ, relCapPair_apply]

end

end Work.Cohomology
