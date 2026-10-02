import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_localFundClass_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the duality map `goodD` in the compact set

`goodD N c W hW K hKW hKc k m hkm : H^k(W, W∖K) → H_m(W)` is the cap product with the local
fundamental class `localFundClass N c W hW K hKW hKc ∈ H_N(W, W∖K)` of `c` at `K`
(`Work.Cohomology.goodD`).

For `K ⊆ K'` inside the open set `W` the pair `(W, W∖K)` maps to the pair `(W, W∖K')` (the
direct image is the *enlargement* `pdRelComplexEnlarge W h` on relative cochains, the inverse
image the enlargement `pdRelChainsEnlarge W h` on relative chains), and the two duality maps
are compatible with these maps:

  `goodD_K' (pdRelComplexEnlarge W h x) = goodD_K x`,

i.e. `x ⌢ μ_{K'} = (x|_{(W,W∖K')}) ⌢ μ_{K'}` where `μ_{K'}` pushes to `μ_K`.  This is the
statement that the compactly supported duality map is compatible with the transition maps of
the filtered colimit `H^k_c(W) = colim_K H^k(W, W∖K)`.

The proof is the naturality `Crux.relCapPair_natural` of the relative cap product under the
identity map of pairs `(W, W∖K) → (W, W∖K')` together with the naturality
`pd_localFundClass_natural` of the local fundamental class.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

open HomologicalComplex

noncomputable section

theorem pd_goodD_natural {M : TopCat} [T2Space M] (N : ℕ)
    (c : (singularChains ℤ M).homology N)
    (W : Set M) (hW : IsOpen W) {K K' : Set M} (h : K ⊆ K')
    (hKW : K ⊆ W) (hK'W : K' ⊆ W) (hKc : IsCompact K) (hK'c : IsCompact K')
    (k m : ℕ) (hkm : k + m = N)
    (x : (relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :
    goodD N c W hW K' hK'W hK'c k m hkm
        ((HomologicalComplex.homologyMap (pdRelComplexEnlarge W h) k) x)
      = goodD N c W hW K hKW hKc k m hkm x := by
  -- Remove the degree bookkeeping `hkm`: both sides live in `H_{k+m}`.
  subst hkm
  -- Unfold the duality maps into cap products with the local fundamental classes.
  simp only [goodD]
  -- Naturality of the relative cap product for the identity map of pairs
  -- `(W, W∖K) → (W, W∖K')`.
  have hnat := Crux.relCapPair_natural (X₁ := TopCat.of W) (X₂ := TopCat.of W)
      (pdRelSub W K') (pdRelSub W K) (𝟙 (TopCat.of W)) (pdRelSub_mono_id h) k m x
      (localFundClass (k + m) c W hW K' hK'W hK'c)
  -- The cochain enlargement is the pair map of `relCapPair_natural`.
  have hbridge : relComplexMap ℤ (pdRelSub W K') (pdRelSub W K) (𝟙 (TopCat.of W))
        (pdRelSub_mono_id h) = pdRelComplexEnlarge W h := by
    rw [pdRelComplexEnlarge]
  rw [hbridge] at hnat
  -- The chain enlargement is the pair map of `relCapPair_natural`.
  rw [pdRelChainsEnlarge_eq_relChainsMapOf W h] at hnat
  -- The class at `K'` pushes forward to the class at `K`.
  rw [pd_localFundClass_natural (k + m) c W hW h hKW hK'W hKc hK'c] at hnat
  -- The pushforward along the identity chain map is the identity.
  have hid : HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of W) (TopCat.of W) (𝟙 (TopCat.of W))) m
      = 𝟙 ((singularChains ℤ (TopCat.of W)).homology m) := by
    rw [chainMap_id', HomologicalComplex.homologyMap_id]
  rw [hid] at hnat
  simpa using hnat

end

end Work.Cohomology
