import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.SES.Connecting
import Submission.Work.AbsoluteKummer.SES.deltaH2_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.SES

theorem exists_connecting_exact_H2 {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] (S : Work.AbsoluteKummer.ShortExactSeq G M N P) : ∃ δ : Work.AbsoluteKummer.H1 G P →+ Work.AbsoluteKummer.H2 G M, (Work.AbsoluteKummer.mapH1 S.pi S.pi_equivariant).range = δ.ker ∧ δ.range = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker := by
  exact ⟨S.deltaH2, range_mapH1_eq_ker_deltaH2 S, range_deltaH2_eq_ker_mapH2 S⟩

end Work.AbsoluteKummer.SES
