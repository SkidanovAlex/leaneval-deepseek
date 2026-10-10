import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.ker_le_range_mapH0
import Submission.Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

theorem exists_connecting_exact {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : ∃ δ : Work.AbsoluteKummer.H0 G P →+ Work.AbsoluteKummer.H1 G M, (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range = δ.ker ∧ δ.range = (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant).ker := by
  refine ⟨S.delta, le_antisymm S.range_mapH0_le_ker_delta (ker_le_range_mapH0 S),
    le_antisymm S.range_delta_le_ker_mapH1 (ker_mapH1_le_range_delta S)⟩

end Work.AbsoluteKummer.SES
