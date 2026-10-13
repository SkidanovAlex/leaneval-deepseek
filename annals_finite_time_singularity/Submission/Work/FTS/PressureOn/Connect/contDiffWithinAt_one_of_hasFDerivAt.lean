import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem contDiffWithinAt_one_of_hasFDerivAt {f : Work.FTS.PressureOn.R3 × ℝ → ℝ}
    {f' : Work.FTS.PressureOn.R3 × ℝ → (Work.FTS.PressureOn.R3 × ℝ →L[ℝ] ℝ)}
    {s : Set (Work.FTS.PressureOn.R3 × ℝ)} {z : Work.FTS.PressureOn.R3 × ℝ} (hs : s ∈ nhds z)
    (h : ∀ y ∈ s, HasFDerivAt f (f' y) y) (hc : ContinuousOn f' s) :
    ContDiffWithinAt ℝ 1 f s z := by
  -- `s` is a neighbourhood of `z`, so `C¹` at `z` implies `C¹` within `s` at `z`; and
  -- `C¹` at a point is exactly the existence of a derivative field that is continuous on a
  -- neighbourhood of the point and differentiates `f` at every point of it.
  exact ((contDiffAt_one_iff (𝕜 := ℝ) (f := f) (x := z)).mpr ⟨f', s, hs, hc, h⟩).contDiffWithinAt

end Work.FTS.PressureOn.Connect
