import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Weyl

/-- There is a smooth, compactly supported test function on `ℝ³` with non-zero integral.

We use Mathlib's normalised bump function `ContDiffBump.normed`: it is `C^∞`, compactly
supported and its integral is exactly `1`.  (This is the "test function" needed to make the
weak formulation of the Poisson equation for the pressure non-trivial.) -/
theorem exists_smooth_compactSupport_integral_ne_zero :
    ∃ φ : Work.FTS.PressureOn.R3 → ℝ,
      (∀ n : ℕ, ContDiff ℝ n φ) ∧ HasCompactSupport φ ∧ (∫ x, φ x) ≠ 0 := by
  let b : ContDiffBump (0 : Work.FTS.PressureOn.R3) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, fun n => ?_, b.hasCompactSupport_normed, ?_⟩
  · exact b.contDiff_normed
  · rw [b.integral_normed]
    norm_num

end Work.FTS.PressureOn.Weyl
