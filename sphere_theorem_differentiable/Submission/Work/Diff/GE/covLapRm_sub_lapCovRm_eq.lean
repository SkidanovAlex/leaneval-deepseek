import Mathlib
import Submission.Work.Diff.GE.covLapRmAt_eq_sum_cov3Rm
import Submission.Work.Diff.GE.cov3Rm_ricci
import Submission.Work.Diff.GE.cov3Rm_swap
import Submission.Work.Diff.GE.CurvDerivDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

theorem covLapRm_sub_lapCovRm_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.GE.covLapRmAt g x v a b c d - Work.Diff.GE.lapCovRmAt g x v a b c d
      = ∑ m, (- (Submission.Diff.covRm g x
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m)
                (Submission.Diff.onFrame g x m)) a b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) a)
              b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) b)
              c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) c)
              d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) d))
          - (Submission.Diff.rmP g x
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) a) b c d
            + Submission.Diff.rmP g x a
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) b) c d
            + Submission.Diff.rmP g x a b
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) c) d
            + Submission.Diff.rmP g x a b c
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) d))
          - (Submission.Diff.covRm g x (Submission.Diff.onFrame g x m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) a)
              b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) b)
              c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) c)
              d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) d))) := by sorry

end Work.Diff.GE
