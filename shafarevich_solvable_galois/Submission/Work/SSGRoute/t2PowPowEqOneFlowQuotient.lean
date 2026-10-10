import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Submission.Work.SSGRoute.step4_local_target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-- **Exponent of the level-`τ` quotient of the free operator group.**  Every element `x` of
`Work.CohomologicalShrinking.flowQuotient p G n i j = F(n)/F(n)^{(i,j)}` (the quotient of the free
`G`-operator group of rank `n` by Schmidt–Wingberg's refined term
`Work.CohomologicalShrinking.refinedTerm p _ i j = (F_i ∩ F^j)F_{i+1}`) satisfies `x ^ (p ^ i) = 1`.

Indeed `refinedTerm p _ i j ≥ Work.CohomologicalShrinking.pSeries p _ (i+1) =
Work.Shrinking.pCentralSeries p _ i`, and the `p`-central series satisfies
`x ^ (p ^ i) ∈ Work.Shrinking.pCentralSeries p _ i` for every `x`.
There is an existing `Work.SSGRoute.flowQuotient_pow_eq_one` with a superfluous `[Fintype G]`
hypothesis, proved by exactly this argument; the point here is to remove that hypothesis (the
argument uses only `Work.ProP.pow_pow_mem_pCentralSeries`, which holds for every group). -/
theorem t2PowPowEqOneFlowQuotient (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (x : Work.CohomologicalShrinking.flowQuotient p G n i j) : x ^ (p ^ i) = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G n i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) x
  rw [← map_pow (QuotientGroup.mk' _) y (p ^ i), QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmem : ((y : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) :
      Work.Shrinking.freeOperatorGroup G n) ^ (p ^ i)
      ∈ Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G n) i :=
    Work.ProP.pow_pow_mem_pCentralSeries p (Work.Shrinking.freeOperatorGroup G n) i _
  have hle : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G n) i
      ≤ flowTerm p G n i j := by
    rw [flowTerm, refinedTerm]
    exact le_sup_right
  exact hle (by simpa using hmem)

end Work.SSGRoute
