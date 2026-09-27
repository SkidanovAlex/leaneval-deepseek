/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cycle-level cross product

For cycles `c ∈ Z_p(X)`, `d ∈ Z_q(Y)` of two simplicial sets we produce a cycle `ω` of
`X ⊗ Y` in degree `p + q` such that the cup product of the pullbacks of arbitrary
cocycles `u`, `v` pairs with `ω` to the product of the pairings `⟨u,c⟩ · ⟨v,d⟩`.

The cycle is the **Eilenberg–Zilber shuffle sum**

`ω = Σ_{a ∈ c.support} Σ_{b ∈ d.support} (c a * d b) • EZ(a ⊗ b)`

(see `Work.Cohomology.ezChainB`).  Three facts about it are used, each proved in its own file:

* `Work.Cohomology.ezChainB_sum_cycle`: for cycles `c`, `d` the shuffle sum is a cycle
  (the Eilenberg–Zilber shuffle lemma),
* `Work.Cohomology.ezChainB_sum_pairing`: evaluated against the cup product of two
  *normalized* cocycles it gives `⟨u,c⟩ · ⟨v,d⟩` (only the shuffle `{0,…,p-1}` contributes),
* `Work.Cohomology.normalized_rep`: every cocycle is cohomologous to a normalized one.

Since a coboundary pairs to zero with a cycle, the pairing only depends on the cohomology
classes of `u` and `v`
(`Work.Cohomology.seval_cup_eq_of_cohomologous`, `Work.Cohomology.seval_eq_of_sub_mem_boundaries`),
which transfers the normalized statement to all cocycles.
-/
import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.ezChainB_sum_cycle
import Submission.Work.Cohomology.ezChainB_sum_pairing
import Submission.Work.Cohomology.normalized_rep
import Submission.Work.Cohomology.seval_cup_eq_of_cohomologous
import Submission.Work.Cohomology.seval_eq_of_sub_mem_boundaries

namespace Work.Cohomology

theorem exists_cycle_cross {X Y : SSet.{0}} {p q : ℕ}
    (c : Submission.Cohomology.SChain X ℚ p) (d : Submission.Cohomology.SChain Y ℚ q)
    (hc : c ∈ Submission.Cohomology.chainCycles X ℚ p)
    (hd : d ∈ Submission.Cohomology.chainCycles Y ℚ q) :
    ∃ ω : Submission.Cohomology.SChain
        (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q),
      ω ∈ Submission.Cohomology.chainCycles
        (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q) ∧
      ∀ (u : Submission.Cohomology.Cochain X ℚ p) (v : Submission.Cohomology.Cochain Y ℚ q),
        Submission.Cohomology.coboundary X ℚ p u = 0 →
        Submission.Cohomology.coboundary Y ℚ q v = 0 →
        Submission.Cohomology.seval
          (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q)
          (Submission.Cohomology.cupOf
            (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ rfl
            (Submission.Cohomology.pullbackCo ℚ
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u)
            (Submission.Cohomology.pullbackCo ℚ
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v)) ω
          = Submission.Cohomology.seval X ℚ p u c * Submission.Cohomology.seval Y ℚ q v d := by
  refine ⟨∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b, ?_, ?_⟩
  · exact ezChainB_sum_cycle c d hc hd
  · intro u v hu hv
    have hucyc : u ∈ Submission.Cohomology.cycles X ℚ p :=
      (Submission.Cohomology.mem_cycles_iff u).mpr hu
    have hvcyc : v ∈ Submission.Cohomology.cycles Y ℚ q :=
      (Submission.Cohomology.mem_cycles_iff v).mpr hv
    obtain ⟨u₁, hu₁c, hu₁n, hu₁b⟩ := normalized_rep u hucyc
    obtain ⟨v₁, hv₁c, hv₁n, hv₁b⟩ := normalized_rep v hvcyc
    rw [seval_cup_eq_of_cohomologous
        (ω := ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b)
        (hω := ezChainB_sum_cycle c d hc hd)
        (u := u) (u' := u₁) (v := v) (v' := v₁)
        hucyc hvcyc hu₁c hv₁c hu₁b hv₁b]
    rw [seval_eq_of_sub_mem_boundaries c hc hu₁b,
        seval_eq_of_sub_mem_boundaries d hd hv₁b]
    exact ezChainB_sum_pairing c d u₁ v₁ hu₁c hv₁c hu₁n hv₁n

end Work.Cohomology
