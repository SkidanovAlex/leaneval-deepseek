import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.finite_freeGroup_quotient_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `M ≤ N` are normal subgroups of a group `G` and `G ⧸ M` is finite, then so is `G ⧸ N`:
`G ⧸ N` is a quotient of `G ⧸ M`, via the canonical isomorphism
`(G ⧸ M) ⧸ (N/M) ≃* G ⧸ N` of `QuotientGroup.quotientQuotientEquivQuotient`. -/
private theorem finite_quotient_of_le {G : Type*} [Group G] (M N : Subgroup G) [M.Normal] [N.Normal]
    (h : M ≤ N) (hfin : Finite (G ⧸ M)) : Finite (G ⧸ N) := by
  haveI : Finite (G ⧸ M) := hfin
  exact Finite.of_equiv _ (QuotientGroup.quotientQuotientEquivQuotient M N h).toEquiv

/-- If `N` contains the `k`-th term `P_k` of the descending `2`-central series of a free group on a
finite generating set `X`, then `FreeGroup X ⧸ N` is finite.

Indeed `FreeGroup X ⧸ P_k` is finite (`Work.Shrinking.finite_freeGroup_quotient_pCentralSeries`:
the free group on a finite set is finitely generated, and its `p`-central quotients are finite),
and `N ⊇ P_k` makes `FreeGroup X ⧸ N` a quotient of `FreeGroup X ⧸ P_k`. -/
theorem finite_quotient_pCentralSeries
    {X : Type*} [Finite X] (k : ℕ) (N : Subgroup (FreeGroup X)) [N.Normal]
    (hk : Work.Shrinking.pCentralSeries 2 (FreeGroup X) k ≤ N) :
    Finite (FreeGroup X ⧸ N) := by
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (Work.Shrinking.pCentralSeries 2 (FreeGroup X) k).Normal :=
    Work.Shrinking.pCentralSeries_normal 2 (FreeGroup X) k
  exact finite_quotient_of_le (G := FreeGroup X) _ N hk
    (Work.Shrinking.finite_freeGroup_quotient_pCentralSeries 2 X k)

end Work.SSGRoute
