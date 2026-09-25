import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Shafarevich.Rank.le_relationRankWith
import Submission.Work.Tower.Shafarevich.Rank.generatorRank_le_iff
import Submission.Work.Tower.Shafarevich.Rank.relationRankWith_le_iff
import Submission.Work.Tower.Shafarevich.Rank.ker_comp_mk_eq

namespace Work.Tower.Shafarevich.Rank

/-- **Relation rank does not drop by more than the number of killed generators.**

If `N` is the normal closure of `k` elements `g : Fin k → G` of a finite group `G`, and `d` is at
least the generator rank of `G`, then `G ⧸ N` admits a presentation with `d` generators and at most
`relationRankWith G d + k` relators.

Indeed, take a `d`-generator presentation of `G` with `relationRankWith G d` relators (which exists
because `relationRankWith` is attained, `G` being finite).  Killing the `k` elements `g i`
corresponds to adjoining the `k` relators "lift of `g i` is trivial", so `G ⧸ N` inherits a
`d`-generator presentation with `relationRankWith G d + k` relators.  This is the estimate used in
Shafarevich's relation-rank inequality. -/
theorem relationRankWith_quotient_le {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (d k : ℕ) (g : Fin k → G) (hN : N = Subgroup.normalClosure (Set.range g))
    (hd : Work.Tower.generatorRank G ≤ d) :
    Work.Tower.relationRankWith (G ⧸ N) d ≤ Work.Tower.relationRankWith G d + k := by
  -- `G` admits a surjection from the free group on `d` generators, since `d ≥ generatorRank G`.
  have hd' : ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ :=
    (generatorRank_le_iff d).mp hd
  -- Since `relationRankWith` is attained, there is a `d`-generator presentation of `G` with
  -- exactly `relationRankWith G d` relators.
  obtain ⟨φ, hφ, R, hR⟩ :=
    (relationRankWith_le_iff d hd' (Work.Tower.relationRankWith G d)).mp le_rfl
  -- Adjoin the `k` relators killing the generators of `N`.
  obtain ⟨R', hR'⟩ := ker_comp_mk_eq N φ hφ R hR g hN
  -- This exhibits a presentation of `G ⧸ N` with `d` generators and `relationRankWith G d + k`
  -- relators.
  exact le_relationRankWith d _ ⟨(QuotientGroup.mk' N).comp φ,
    (QuotientGroup.mk'_surjective N).comp hφ, R', hR'⟩

end Work.Tower.Shafarevich.Rank
