import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

theorem isSmoothLoop_comp_neg {v : ℝ → ℂ} (hv : IsSmoothLoop v) :
    IsSmoothLoop (fun t : ℝ => v (-t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hv.1.comp contDiff_neg
    simpa [Function.comp_def] using this
  · intro t
    show v (-(t + 2 * π)) = v (-t)
    have h := hv.2.1 (-t - 2 * π)
    have e : -(t + 2 * π) = -t - 2 * π := by ring
    rw [e]
    simpa using h.symm
  · intro t t' h
    obtain ⟨m, hm⟩ := hv.2.2.1 (-t) (-t') h
    refine ⟨-m, ?_⟩
    push_cast
    linarith
  · intro t
    rw [deriv_comp_neg]
    exact neg_ne_zero.mpr (hv.2.2.2 (-t))

end Work.RPB1a
