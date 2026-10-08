import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CPTC

theorem NcardInvolutionSetTopSplit {G : Type} [Group G] [Finite G] (K : Subgroup G) (s : G) :
    (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)).ncard
      = ({z : G | orderOf z = 2 ∧ z ∉ K} ∩ Subgroup.centralizer ({s} : Set G)).ncard
        + (Work.GW2.involutionSet K ∩ Subgroup.centralizer ({s} : Set G)).ncard := by
  -- Split the involutions of `G` centralizing `s` according to whether they lie in `K`.
  set A : Set G := {z : G | orderOf z = 2 ∧ z ∉ K} ∩ Subgroup.centralizer ({s} : Set G) with hA
  set B : Set G := Work.GW2.involutionSet K ∩ Subgroup.centralizer ({s} : Set G) with hB
  have hS : Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({s} : Set G)
      = A ∪ B := by
    ext z
    by_cases hz : z ∈ K
    · simp [Work.GW2.involutionSet, hz, hA, hB]
    · simp [Work.GW2.involutionSet, hz, hA, hB]
  rw [hS, hA, hB]
  -- The two parts are disjoint, so their cardinalities add.
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    rw [hA] at hzA
    rw [hB] at hzB
    exact hzA.1.2 hzB.1.1
  have hcard := Set.ncard_union_add_ncard_inter A B
  have hinter : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  rw [hinter, Set.ncard_empty, add_zero] at hcard
  exact hcard

end Work.CPTC
