import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- `psi` is smooth. -/
theorem contDiff_psi : ContDiff ℝ ⊤ WilkiesDesign.E.psi := by
  unfold WilkiesDesign.E.psi
  refine ContDiff.div contDiff_id ?_ fun x => ?_
  · exact (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun y => by positivity)
  · positivity

end Work.WilE9.Psi
