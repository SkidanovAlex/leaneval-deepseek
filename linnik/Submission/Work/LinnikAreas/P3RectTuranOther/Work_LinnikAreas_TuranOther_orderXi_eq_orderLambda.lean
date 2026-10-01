import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase
import Submission.Work.LinnikAreas.PrincipalZeroCount

namespace Work.LinnikAreas.TuranOther

-- IMPORT WARNING: do NOT import `Submission.Work.LinnikAreas.zetaOrder_eq_xiF` (nor anything
-- importing `Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq`): that family clashes
-- with this file's own import closure. Prove it directly with `analyticOrderAt_mul` from
-- `DhK.Xi_eq_half_mul` (on `u ≠ 0,1`) and `analyticOrderNatAt_of_not_analyticAt` at `0,1`.
theorem orderXi_eq_orderLambda (u : ℂ) :
    analyticOrderNatAt Work.LinnikAreas.DhK.Xi u
      = analyticOrderNatAt completedRiemannZeta u := by
  by_cases h0 : u = 0
  · subst h0
    have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Work.LinnikAreas.DhK.Xi_zero]; norm_num))
    rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 0 = 0 from by
          simp [analyticOrderNatAt, hx],
      analyticOrderNatAt_of_not_analyticAt
        Work.LinnikAreas.not_analyticAt_completedZeta_zero]
  · by_cases h1 : u = 1
    · subst h1
      have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 1 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by
          rw [show Work.LinnikAreas.DhK.Xi 1 = 1 / 2 by simp [Work.LinnikAreas.DhK.Xi]]
          norm_num))
      rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 1 = 0 from by
            simp [analyticOrderNatAt, hx],
        analyticOrderNatAt_of_not_analyticAt
          Work.LinnikAreas.not_analyticAt_completedZeta_one]
    · exact Work.LinnikAreas.analyticOrderNatAt_xiC_eq u h0 h1

end Work.LinnikAreas.TuranOther
