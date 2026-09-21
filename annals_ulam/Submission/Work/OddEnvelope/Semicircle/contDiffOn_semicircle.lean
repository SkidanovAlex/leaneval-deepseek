import Mathlib
import Submission.Work.OddEnvelope.Defs

namespace Work.OddEnvelope.Semicircle

theorem contDiffOn_semicircle :
    ContDiffOn ℝ (⊤ : WithTop ENat) Work.OddEnvelope.semicircle (Set.Ioo (-1 : ℝ) 1) := by
  unfold Work.OddEnvelope.semicircle
  apply ContDiffOn.sqrt
  · fun_prop
  · intro x hx
    have hx1 : -1 < x := (Set.mem_Ioo.mp hx).1
    have hx2 : x < 1 := (Set.mem_Ioo.mp hx).2
    have hsq : x ^ 2 < 1 := by nlinarith
    intro h
    nlinarith [hsq, h]

end Work.OddEnvelope.Semicircle
