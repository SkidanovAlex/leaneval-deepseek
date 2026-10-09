import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.le_subgroup_of_isProP_of_coprime_quotient
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.Ramification

/-- **The first higher ramification subgroup is the wild inertia.**

For `A` a valuation subring of `L/K` with finite decomposition subgroup, the subgroup
`G_1 ≤ G_0` of the decomposition subgroup is the maximal normal pro-`p` subgroup of `G_0`,
i.e. `NK.LocalTame.IsWildInertia p ↥G_0 ↥G_1` — provided `G_1` is pro-`p` and `p` is coprime
to the index `[G_0 : G_1]`.

The point is that the maximality is *forced* by the two hypotheses: a normal pro-`p` subgroup
`N ◁ G_0` maps into the quotient `G_0/G_1`, so `N/(N ∩ G_1)` is simultaneously a quotient of a
pro-`p` group (hence of `p`-power order) and a subgroup of a group of order coprime to `p`
(hence trivial); this is `le_subgroup_of_isProP_of_coprime_quotient`.  Normality of `G_1 ◁ G_0`
comes from normality of `G_1` in the whole decomposition subgroup
(`ramificationSubgroup_normal`). -/
theorem isWildInertia_ramificationSubgroup_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] {p : ℕ} (hp : p.Prime)
    (hpro : NK.LocalTame.IsProP p ↥((NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
      (NK.Ramification.ramificationSubgroup (K := K) A 0)))
    (hcop : Nat.Coprime p (Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A 0) ⧸
      (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)))) :
    NK.LocalTame.IsWildInertia p ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)
      ((NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)) := by
  haveI : Finite ↥(ramificationSubgroup (K := K) A 0) := inferInstance
  haveI : ((ramificationSubgroup (K := K) A 1).subgroupOf
      (ramificationSubgroup (K := K) A 0)).Normal :=
    (ramificationSubgroup_normal A 1).subgroupOf _
  refine ⟨inferInstance, hpro, ?_⟩
  intro N hN hNp
  haveI : N.Normal := hN
  exact le_subgroup_of_isProP_of_coprime_quotient hp _ N hNp hcop

end NK.Ramification
