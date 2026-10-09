import Mathlib
import Submission.Work.GroupCohomology.Inflation
import Submission.Work.GroupCohomology.Functoriality
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- The composite `H²(G ⧸ N, A^N) --inf--> H²(G, A) --res--> H²(N, A)` is zero: the restriction of an inflated `2`-cocycle to `N × N` is the constant cocycle at `c (1,1)`, which is a coboundary.  This is the `⊆` half of the degree-`2` inflation–restriction exactness. -/
theorem resH2_infH2_eq_zero {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] :
    (Work.GroupCohomology.resH2 (A := A) G N).comp
      (Work.GroupCohomology.infH2 (A := A) N) = 0 := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H2_induction_on with
  | h c =>
    rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, infH2_H2π, resH2_H2π,
      H2pi_eq_zero_iff, mem_B2_iff]
    refine ⟨fun _ => (c.1 (1, 1) : A), ?_⟩
    funext p
    obtain ⟨p1, p2⟩ := p
    rw [d1_apply, resZ2_coe, resCochain2_apply, infCocycle2_apply]
    have hm1 : QuotientGroup.mk' N (p1 : G) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact p1.2
    have hm2 : QuotientGroup.mk' N (p2 : G) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact p2.2
    rw [hm1, hm2]
    have hfix : p1 • (c.1 (1, 1) : A) = (c.1 (1, 1) : A) := (c.1 (1, 1)).2 p1
    rw [hfix]
    abel

end Work.GroupCohomology
