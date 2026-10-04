import Mathlib
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.cov2Rm_ricci_defs
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

theorem cov2Rm_ricci_pt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (u p a b c d : TangentSpace I x) :
    Work.Diff.GE.cov2Rm g x u p a b c d - Work.Diff.GE.cov2Rm g x p u a b c d
      = - (Submission.Diff.rmP g x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x u p a) b c d
          + Submission.Diff.rmP g x a (Submission.Diff.rmVec (Submission.Diff.lcOf g) x u p b) c d
          + Submission.Diff.rmP g x a b (Submission.Diff.rmVec (Submission.Diff.lcOf g) x u p c) d
          + Submission.Diff.rmP g x a b c (Submission.Diff.rmVec (Submission.Diff.lcOf g) x u p d)) := by sorry

end Work.Diff.GE
