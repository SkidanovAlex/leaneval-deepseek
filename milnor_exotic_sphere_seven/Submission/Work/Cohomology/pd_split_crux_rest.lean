import Mathlib
import Submission.Work.Cohomology.pd_union_split

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

namespace Work.Cohomology

/-- **The "splitting" crux of the two-piece cover, in the form in which the `A+B` decomposition of
the representing cocycle is already available.**

This is `Work.Cohomology.pd_union_split` applied to the class `homologyπ k z` of the given cycle:
once the cycle is fixed, the supplementary data (`φA`, `φB` and the decomposition of its underlying
cochain) are not needed, because the conclusion only depends on the homology class of `z`. -/
theorem pd_split_crux_rest {M : TopCat} [T2Space M] {N : ℕ}
    {c : (Work.Cohomology.singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Work.Cohomology.Good N c U hU) (hVV : Work.Cohomology.Good N c V hV)
    (hII : Work.Cohomology.Good N c (U ∩ V) hI)
    (k m : ℕ) (hkm : k + m = N) (hm : 1 ≤ m)
    {K₁ K₂ : Set M} (hK₁U : K₁ ⊆ U) (hK₂V : K₂ ⊆ V)
    (hK₁c : IsCompact K₁) (hK₂c : IsCompact K₂)
    (z : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).cycles k)
    (φA : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁)).X k)
    (φB : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂)).X k)
    (hφ : ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
          (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).iCycles k z).1 = φA.1 - φB.1)
    (hx : Work.Cohomology.goodD N c (U ∪ V : Set M) (hU.union hV) (K₁ ∪ K₂)
            (Set.union_subset (hK₁U.trans Set.subset_union_left)
              (hK₂V.trans Set.subset_union_right)) (hK₁c.union hK₂c) k m hkm
            ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k z) = 0) :
    ∃ (K₁' K₂' : Set M) (h₁ : K₁ ⊆ K₁') (h₂ : K₂ ⊆ K₂') (hK₁'U : K₁' ⊆ U) (hK₂'V : K₂' ⊆ V)
      (hK₁'c : IsCompact K₁') (hK₂'c : IsCompact K₂')
      (x₁ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₁')).homology k)
      (x₂ : (Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
              (Work.Cohomology.pdRelSub (U ∪ V : Set M) K₂')).homology k),
      (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
        (Set.union_subset (h₁.trans Set.subset_union_left)
          (h₂.trans Set.subset_union_right) : K₁ ∪ K₂ ⊆ K₁' ∪ K₂')) k)
          ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
            (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k z)
        = (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_left : K₁' ⊆ K₁' ∪ K₂')) k) x₁
          - (HomologicalComplex.homologyMap (Work.Cohomology.pdRelComplexEnlarge (U ∪ V : Set M)
            (Set.subset_union_right : K₂' ⊆ K₁' ∪ K₂')) k) x₂ :=
  pd_union_split hU hV hI hUU hVV hII k m hkm hm hK₁U hK₂V hK₁c hK₂c
    ((Work.Cohomology.relComplex ℤ (TopCat.of (U ∪ V : Set M))
      (Work.Cohomology.pdRelSub (U ∪ V : Set M) (K₁ ∪ K₂))).homologyπ k z) hx

end Work.Cohomology
