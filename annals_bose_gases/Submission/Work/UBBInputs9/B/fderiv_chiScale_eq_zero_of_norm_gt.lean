import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Const
import Submission.Work.UBBInputs9.B.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B

open MeasureTheory Metric Filter
open scoped Topology

/-- `chiScale s` vanishes on the open set `‖y‖ > s/2`, so it is eventually equal there to the
zero function and hence has vanishing derivative. -/
theorem fderiv_chiScale_eq_zero_of_norm_gt {s : ℝ} (hs : 0 < s) {y v : EuclideanSpace ℝ (Fin 3)} (h : s / 2 < ‖y‖) :
    fderiv ℝ (Submission.BoseGases.chiScale s) y v = 0 := by
  have hzero : ∀ z : EuclideanSpace ℝ (Fin 3), s / 2 < ‖z‖ →
      Submission.BoseGases.chiScale s z = 0 := by
    intro z hz
    by_contra hne
    have := Submission.BoseGases.chiScale_support_le hs hne
    linarith
  have hev : (fun z => Submission.BoseGases.chiScale s z) =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds h] with z hz
    exact hzero z hz
  rw [hev.fderiv_eq]
  simp

end Work.UBBInputs9.B
