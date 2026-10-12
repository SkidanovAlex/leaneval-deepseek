import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

theorem dlThreshold_eq_delivered_shape (c C μ av R s ΓK P : ℝ) :
    (c * (((P / s ^ 3) - μ) ^ 2 / (1 + (P / s ^ 3) / μ)) - (1 / 2) * μ ^ 2)
        * (8 * Real.pi * av * s ^ 3)
      - C * μ ^ 2 * av * ((R / s) ^ 2 + ΓK) * s ^ 3 - C * μ * av
    = Work.FockBridge.dlThreshold c C μ av (s ^ 3) ((R / s) ^ 2 + ΓK) P := by
  simp only [Work.FockBridge.dlThreshold, Work.FockBridge.dlDensityThreshold,
    Work.FockBridge.dlDensityCoeff]
  ring

end Work.SlotWord
