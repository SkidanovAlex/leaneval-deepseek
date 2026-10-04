import Mathlib
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.onFrameONfield
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.kato_covRm_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

theorem covLapRmAt_eq_sum_cov3Rm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.GE.covLapRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3Rm g x v (Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x m) a b c d := by sorry

end Work.Diff.GE
