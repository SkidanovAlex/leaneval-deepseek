import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_of_close

namespace Work.OddBridge

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

theorem isEnvelopeCurve_of_curveData (n : ℕ) {h x y : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    Work.OddEnvelope.IsEnvelopeCurve h x y := by
  -- `h` vanishes at `0`, since `0` lies strictly below the support window `[4/5, 9/10]`.
  have h0 : h 0 = 0 := by
    by_contra hne
    have hmem := hhsupp hne
    rw [Set.mem_Icc] at hmem
    rw [Work.OddVolterra.tau] at hmem
    norm_num at hmem
  -- The window of `CurveData` is the window of `IsEnvelopeCurve` (`tau = 1/10` definitionally).
  have hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau) := hhsupp
  exact Work.OddEnvelope.Close.isEnvelopeCurve_of_close (hδ := le_rfl)
    hdata.smooth_x hdata.smooth_y hh.contDiffOn hdata.deriv_x_neg hdata.deriv_y_neg
    hdata.tendsto_x hdata.tendsto_y hdata.tail_x hdata.tail_y h0 hsupp
    hdata.close_x hdata.close_y hdata.close_h

end

end Work.OddBridge
