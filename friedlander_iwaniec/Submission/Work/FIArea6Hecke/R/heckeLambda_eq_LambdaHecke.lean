import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.mellin_cut_facts
import Submission.Work.FIArea5.S16Hecke.integral_inv_scale
import Submission.Work.FIArea5.S16Hecke.cpow_inv_scale
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta

set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped Topology

noncomputable section

/-- The Mellin identity `mellin_thetaHol`, stated in the `mellin` normalisation
`mellin f s = ∫ u in (0,∞), u^{s-1} • f u`. -/
lemma mellin_thetaHol_eq (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 + (m : ℝ) / 2 < s.re) :
    mellin (Work.FIArea5.S16Hecke.thetaHol chi m) s =
      Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) (s - (m : ℂ) / 2) := by
  rw [mellin, ← Work.FIArea5.S16Hecke.mellin_thetaHol chi m hchi hs]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [smul_eq_mul]; ring

end

end Work.FIArea6Hecke.R
