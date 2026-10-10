import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H3Map

theorem range_deltaH3_le_ker_mapH3 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    S.deltaH3.range ≤ (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant).ker := by
  rintro y ⟨x, rfl⟩
  rw [AddMonoidHom.mem_ker]
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G P).comap (Work.AbsoluteKummer.Z2 G P).subtype) x
  rw [show x = Work.AbsoluteKummer.H2π G P c from hc.symm]
  rw [S.deltaH3_H2π, Work.SSGRoute.H3Map.mapH3_H3π, Work.SSGRoute.H3π_eq_zero_iff G _,
    Work.SSGRoute.mem_B3_iff]
  refine ⟨S.liftCochain2 (c : G × G → P),
    Work.AbsoluteKummer.ShortExactSeq.isLocallyConstant_liftCochain2 S c.2.2, ?_⟩
  funext p
  rw [Work.SSGRoute.H3Map.mapZ3_apply]
  have hmem : Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p ∈ S.iota.range := by
    rw [S.range_iota_eq_ker_pi, AddMonoidHom.mem_ker]
    exact Work.AbsoluteKummer.ShortExactSeq.pi_d2_liftCochain2 S
      (Work.SSGRoute.d2_eq_zero_of_mem_Z2 c.2.1) p
  exact (S.iota_iotaInv hmem).symm

end Work.SSGRoute.H3Map
