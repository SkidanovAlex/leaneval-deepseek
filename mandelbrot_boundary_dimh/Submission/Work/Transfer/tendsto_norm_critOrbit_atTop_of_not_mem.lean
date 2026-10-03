import Mathlib
import Submission.Work.Transfer.Setup

namespace Work.Transfer

open LeanEval.Dynamics.MandelbrotBoundary Filter

/-- At an escaping parameter `c ∉ Mandelbrot`, the norms of the critical orbit
`critOrbit m c = (Tc c)^[m] c = (Tc c)^[m+1] 0` tend to `+∞`. -/
theorem tendsto_norm_critOrbit_atTop_of_not_mem {c : ℂ} (hM : MandelDim.MsetStatement)
    (hc : c ∉ LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot) :
    Filter.Tendsto (fun m : ℕ => ‖Work.Transfer.critOrbit m c‖) Filter.atTop Filter.atTop := by
  have hiter : Filter.Tendsto (fun n : ℕ => ‖(Tc c)^[n] 0‖) Filter.atTop Filter.atTop :=
    hM.2.2.2.1 c hc
  have hreindex : (fun m : ℕ => ‖critOrbit m c‖) = fun m : ℕ => ‖(Tc c)^[m + 1] 0‖ := by
    funext m
    rw [critOrbit_eq_iterate_zero]
  rw [hreindex]
  exact hiter.comp (Filter.tendsto_add_atTop_nat 1)

end Work.Transfer
