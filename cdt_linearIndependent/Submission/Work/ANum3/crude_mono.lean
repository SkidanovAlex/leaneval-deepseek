import Mathlib
import Submission.Work.ANum3.CrudeDefs

namespace Work.ANum3

/-- **Monotonicity of the crude second-derivative bound.**

`crude r A E C1 w wm1 wlo Qp Qhi Slo Shi` is increasing in each of
`A, E, C1, w, wm1, Qp, Qhi, Shi` and decreasing in the two *lower* bounds
`Slo, wlo` (which occur in the denominators).  Hence if every "upper" datum of
the left-hand tuple is bounded by the corresponding "upper" datum of the
right-hand tuple, and every "lower" datum of the right-hand tuple is bounded by
the corresponding "lower" datum of the left-hand tuple, the whole expression
increases. -/
theorem crude_mono {r A A' E E' C1 C1' w W wm1b wm1 wloL Wlo QpL Qp QhiL Qhi SloL Slo ShiL Shi : ℝ}
    (hr : 0 < r) (hA0 : 0 ≤ A) (hA : A ≤ A') (hE0 : 0 ≤ E) (hE : E ≤ E')
    (hC10 : 0 ≤ C1) (hC1 : C1 ≤ C1') (hw0 : 0 ≤ w) (hw : w ≤ W)
    (hwm1b0 : 0 ≤ wm1b) (hwm1b : wm1b ≤ wm1) (hQpL0 : 0 ≤ QpL) (hQpL : QpL ≤ Qp)
    (hQhiL0 : 0 ≤ QhiL) (hQhiL : QhiL ≤ Qhi) (hSlo0 : 0 < Slo) (hSloL0 : 0 < SloL)
    (hSlo : Slo ≤ SloL) (hShiL0 : 0 ≤ ShiL) (hShiL : ShiL ≤ Shi)
    (hWlo0 : 0 < Wlo) (hWloL0 : 0 < wloL) (hWlo : Wlo ≤ wloL) :
    Work.ANum3.crude r A E C1 w wm1b wloL QpL QhiL SloL ShiL
      ≤ Work.ANum3.crude r A' E' C1' W wm1 Wlo Qp Qhi Slo Shi := by
  -- nonnegativity facts for the right-hand ("upper") data, obtained from the
  -- left-hand nonnegativity and the monotonicity hypotheses
  have hA'0 : 0 ≤ A' := le_trans hA0 hA
  have hE'0 : 0 ≤ E' := le_trans hE0 hE
  have hC1'0 : 0 ≤ C1' := le_trans hC10 hC1
  have hW0 : 0 ≤ W := le_trans hw0 hw
  have hwm10 : 0 ≤ wm1 := le_trans hwm1b0 hwm1b
  have hQp0 : 0 ≤ Qp := le_trans hQpL0 hQpL
  have hQhi0 : 0 ≤ Qhi := le_trans hQhiL0 hQhiL
  have hShi0 : 0 ≤ Shi := le_trans hShiL0 hShiL
  -- strict positivity of the denominators (`SloL ≥ Slo > 0`, `wloL ≥ Wlo > 0`)
  have hSloL0' : 0 < SloL := lt_of_lt_of_le hSlo0 hSlo
  have hwloL0' : 0 < wloL := lt_of_lt_of_le hWlo0 hWlo
  unfold Work.ANum3.crude
  gcongr

end Work.ANum3
