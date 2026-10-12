import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxOneBody.ProfDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxOneBody

theorem prof_support (R : ℝ) (hR : 1 < R) :
    Function.support (fun y : EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxOneBody.Prof ((‖y‖ - 1) / (R - 1))) = Metric.ball 0 R := by
  have hR1 : 0 < R - 1 := by linarith
  ext y
  simp only [Function.mem_support, ne_eq, Prof_ne_zero_iff, Metric.mem_ball, dist_zero_right]
  rw [div_lt_one hR1]
  constructor <;> intro h <;> linarith

end Work.SmallBoxOneBody
