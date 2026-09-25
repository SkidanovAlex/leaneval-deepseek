import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.QuotientRank
import Submission.Work.Tower.Shafarevich.Rank.generatorRank_le_iff
import Submission.Work.Tower.Shafarevich.Rank.generatorRank_le_of_surjective
import Submission.Work.Tower.Shafarevich.Rank.relationRankWith_quotient_le

/-!
# The tower-cutting step, in the form used by the Golod–Shafarevich argument

Paper Proposition 3.3 / A.8: if `G` is a finite `p`-group, `g₁, …, g_k ∈ Φ(G)`, and `N` is their
normal closure, then `d(G/N) = d(G)` and `r(G/N) ≤ r(G) + k`.  Here `d = generatorRank` and
`r = relationRankWith · (generatorRank ·)`.

This combines `Work.Tower.QuotientRank` (the generator rank is unchanged) with the relation-counting
bound `relationRankWith_quotient_le`.
-/

open scoped Classical

namespace Work.Tower.Shafarevich

set_option linter.unusedVariables false

/-- **Tower cutting** (paper Prop. 3.3 / A.8): quotienting a finite `p`-group `G` by the normal
closure `N` of elements `g i ∈ Φ(G)` leaves the generator rank unchanged and increases the relation
rank by at most `k`. -/
theorem generatorRank_quotient_frattini_and_relationRankWith_le {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G] (hG : IsPGroup p G) (k : ℕ) (g : Fin k → G)
    (hg : ∀ i, g i ∈ frattini G) :
    Work.Tower.generatorRank (G ⧸ Subgroup.normalClosure (Set.range g)) =
        Work.Tower.generatorRank G ∧
      Work.Tower.relationRankWith (G ⧸ Subgroup.normalClosure (Set.range g))
          (Work.Tower.generatorRank G)
        ≤ Work.Tower.relationRankWith G (Work.Tower.generatorRank G) + k := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⧸ Subgroup.normalClosure (Set.range g)) := Quotient.finite _
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · exact Work.Tower.Shafarevich.Rank.generatorRank_le_of_surjective
        (QuotientGroup.mk' (Subgroup.normalClosure (Set.range g)))
        (QuotientGroup.mk'_surjective _)
    · rw [Work.Tower.Shafarevich.Rank.generatorRank_le_iff]
      exact (Work.Tower.QuotientRank (Fact.out : Nat.Prime p) G hG k g hg
        (Work.Tower.generatorRank (G ⧸ Subgroup.normalClosure (Set.range g)))).mpr
        ((Work.Tower.Shafarevich.Rank.generatorRank_le_iff
          (G := G ⧸ Subgroup.normalClosure (Set.range g)) _).mp le_rfl)
  · exact Work.Tower.Shafarevich.Rank.relationRankWith_quotient_le
      (Subgroup.normalClosure (Set.range g)) (Work.Tower.generatorRank G) k g rfl le_rfl

end Work.Tower.Shafarevich
