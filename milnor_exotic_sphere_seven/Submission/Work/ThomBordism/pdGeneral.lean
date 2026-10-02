import Mathlib
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Projective.pd_goodD_univ_iff_capPair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Poincaré duality in *all* degrees, from the `Good` predicate

`Work.Cohomology.Good N c W hW` is the elementwise form of Poincaré–Lefschetz duality for the open
set `W ⊆ M`; for `W = Set.univ` it is the elementwise form of the statement that
`y ↦ y ⌢ c : H^k(M) → H_{N-k}(M)` is bijective.  The workspace had this conclusion only in the
*degree* `k = N/2` (`Work.Cohomology.pd_middleDegree_of_good`, proved with `N = n + n`), which is
all the applications needed; the present file proves it for **arbitrary** bidegrees `k + m = N`.

* `Work.Cohomology.goodD_univ_bijective_gen` — `Good N c Set.univ` gives bijectivity of the duality
  map `goodD N c Set.univ … k m hkm` at the maximal compact set `K = Set.univ` (the degree-general
  form of `goodD_univ_bijective`, which is the internal lemma of `pd_middleDegree_of_good`);
* `Work.Cohomology.pd_capPair_of_good` — the conclusion for `capPair`, by combining the former with
  the already proved general equivalence
  `Work.Projective.pd_goodD_univ_iff_capPair_gen`.

The application in this workspace is the double `D = W ∪_∂W W̄` of a compact `9`-manifold with
boundary: there `N = 9` is odd, so the middle-degree statement does not apply, while the two
bidegrees that matter are `(k, m) = (4, 5)` (giving `H⁴(D;ℚ) ≅ H₅(D;ℚ)`) and `(5, 4)`
(`H⁵(D;ℚ) ≅ H₄(D;ℚ)`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **The duality map at the maximal compact set, from `Good`** (all degrees).

From `Good N c Set.univ` one obtains bijectivity of the duality map at `K = Set.univ`: since
`Set.univ` is cofinal among the compact subsets of `Set.univ`, the filtered colimit degenerates to
the module `H^k(M, M∖M)` itself.  This is `goodD_univ_bijective` (inside
`pd_middleDegree_of_good.lean`) with the middle degree `n + n` replaced by an arbitrary pair
`k + m = N`; the proof is verbatim, since `Good.hit`/`Good.kill` and the naturality of `goodD` are
already stated for arbitrary bidegrees. -/
theorem goodD_univ_bijective_gen {M : TopCat} [CompactSpace M] [T2Space M]
    {N : ℕ} (c : (singularChains ℤ M).homology N)
    (h : Good N c Set.univ isOpen_univ) (k m : ℕ) (hkm : k + m = N) :
    Function.Bijective (fun x : (relComplex ℤ (TopCat.of (Set.univ : Set M))
        (pdRelSub (Set.univ : Set M) Set.univ)).homology k =>
      goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
        isCompact_univ k m hkm x) := by
  -- the duality map is additive in the first variable (it is a cap product)
  have hsub : ∀ x₁ x₂ : (relComplex ℤ (TopCat.of (Set.univ : Set M))
        (pdRelSub (Set.univ : Set M) Set.univ)).homology k,
      goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
          isCompact_univ k m hkm (x₁ - x₂)
        = goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
            isCompact_univ k m hkm x₁
          - goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
            isCompact_univ k m hkm x₂ := by
    intro x₁ x₂
    simp only [goodD, map_sub, LinearMap.sub_apply]
  refine ⟨?_, ?_⟩
  · -- injectivity (via `Good.kill` at the maximal compact set)
    intro x₁ x₂ hx
    have h0 : goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
        isCompact_univ k m hkm (x₁ - x₂) = 0 := by
      rw [hsub x₁ x₂]
      have hxx : goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
          isCompact_univ k m hkm x₁
          = goodD N c Set.univ isOpen_univ Set.univ (Set.subset_univ Set.univ)
            isCompact_univ k m hkm x₂ := hx
      rw [hxx, sub_self]
    obtain ⟨K', hUK', hK'U, hK'c, hkill⟩ :=
      Good.kill h k m hkm Set.univ (Set.subset_univ Set.univ) isCompact_univ (x₁ - x₂) h0
    have hK'eq : K' = Set.univ := Set.Subset.antisymm hK'U hUK'
    subst hK'eq
    rw [pdRelComplexEnlarge_self Set.univ hUK', HomologicalComplex.homologyMap_id] at hkill
    exact sub_eq_zero.mp (by simpa using hkill)
  · -- surjectivity (cofinality of `Set.univ` among the compact subsets of `Set.univ`)
    intro y
    obtain ⟨K, hKU, hKc, x, hx⟩ := Good.hit h k m hkm y
    refine ⟨(HomologicalComplex.homologyMap (pdRelComplexEnlarge Set.univ hKU) k) x, ?_⟩
    rw [← hx]
    exact pd_goodD_natural N c Set.univ isOpen_univ hKU hKU
      (Set.subset_univ Set.univ) hKc isCompact_univ k m hkm x

/-- **Poincaré duality in all degrees, from `Good`.**  If `Good N c Set.univ` holds for a class
`c ∈ H_N(M;ℤ)`, then for every `k + m = N` the cap product `y ↦ y ⌢ c : H^k(M) → H_m(M)` is
bijective. -/
theorem pd_capPair_of_good {N : ℕ} (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (h : Work.Cohomology.Good N c Set.univ isOpen_univ) (k m : ℕ) (hkm : k + m = N) :
    Function.Bijective (fun y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology k =>
      (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) k m) y (hkm ▸ c)) :=
  (Work.Projective.pd_goodD_univ_iff_capPair_gen k m N hkm c).mp
    (goodD_univ_bijective_gen c h k m hkm)

end

end Work.Cohomology
