import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.deltaH2_forward
import Submission.Work.AbsoluteKummer.SES.ker_deltaH2_le_range_mapH1
import Submission.Work.AbsoluteKummer.SES.ker_mapH2_le_range_deltaH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

open Work.AbsoluteKummer

/-- **Exactness at `H¹(G,P)`**: the image of `H¹(π)` is the kernel of the connecting map
`δ : H¹(G,P) → H²(G,M)`. -/
theorem range_mapH1_eq_ker_deltaH2 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    (Work.AbsoluteKummer.mapH1 S.pi S.pi_equivariant).range = S.deltaH2.ker :=
  le_antisymm (range_mapH1_le_ker_deltaH2 S) (ker_deltaH2_le_range_mapH1 S)

/-- **Exactness at `H²(G,M)`**: the image of the connecting map `δ : H¹(G,P) → H²(G,M)` is the
kernel of `H²(ι)`. -/
theorem range_deltaH2_eq_ker_mapH2 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    S.deltaH2.range = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker :=
  le_antisymm (range_deltaH2_le_ker_mapH2 S) (ker_mapH2_le_range_deltaH2 S)

end Work.AbsoluteKummer.SES
