import Mathlib
import Submission.Work.FIArea7.prop232
import Submission.Work.FIArea7.KStarDisc_bound
import Submission.Work.FIArea7.msmooth_sum_bound

namespace Work.FIArea7

/-- FI Prop 23.2 (23.11)-(23.12), unconditional: finish the theorem `Work.FIArea7.prop232` of `Submission/Work/FIArea7/prop232.lean`, whose last line is currently a `sorry` but was intended to be `exact prop232_of KStarDisc_bound msmooth_sum_bound`; both inputs are proved in the workspace (files KStarDisc_bound and msmooth_sum_bound). -/
theorem prop232Done : Work.FIArea7.Prop232 :=
  prop232_of KStarDisc_bound msmooth_sum_bound

end Work.FIArea7
