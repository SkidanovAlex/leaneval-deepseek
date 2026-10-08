import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.isPSolvable_quotient
import Submission.Work.Fitting.pLength_spec
import Submission.Work.Fitting.pLength_le_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_quotient_le`

The `p`-length does not increase when passing to a quotient: for a finite `p`-solvable group
`G` and a normal subgroup `N ◁ G` such that `G ⧸ N` is `p`-solvable,

`ℓ_p(G ⧸ N) ≤ ℓ_p(G)`.

The mathematical content is that a surjective homomorphism carries the upper `p`-series of
the source into that of the target (`pCoreSeries_map_le`): stage by stage, images of
`p`- and `p'`-factors are again `p`- and `p'`-factors.  Hence at the stage
`2 * ℓ_p(G) + 1`, where the series of `G` is already `⊤` (`pLength_spec`), the series of
`G ⧸ N` is `⊤` as well; by `pLength_le_iff` this says exactly `ℓ_p(G ⧸ N) ≤ ℓ_p(G)`.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.Fitting

theorem pLength_quotient_le (p : ℕ) (G : Type*) [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    [Work.Fitting.IsPSolvable p G] [Work.Fitting.IsPSolvable p (G ⧸ N)] :
    Work.Fitting.pLength p (G ⧸ N) ≤ Work.Fitting.pLength p G := by
  letI : Finite (G ⧸ N) := (finite_iff_subgroup_quotient N).mp ‹Finite G› |>.2
  rw [Work.Fitting.pLength_le_iff p (G ⧸ N) (inferInstance) (Work.Fitting.pLength p G)]
  have h := Work.Fitting.pCoreSeries_map_le p G (G ⧸ N) (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (2 * Work.Fitting.pLength p G + 1)
  rw [Work.Fitting.pLength_spec p G (inferInstance),
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  exact top_le_iff.mp h

end Work.Fitting
