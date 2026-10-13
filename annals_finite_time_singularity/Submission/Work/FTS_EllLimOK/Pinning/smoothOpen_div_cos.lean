import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.Pinning

open scoped Real Topology
open MeasureTheory Set Filter

/-- **`SmoothOpen` is stable under division by `cos θ`.**  On the open quadrant
`Q0 = (0,∞) × (0,π/2)` one has `cos θ ≠ 0` (`Real.cos_pos_of_mem_Ioo`), so dividing a
function which is `C^∞` on `Q0` by the (globally `C^∞`) angular factor `cos θ` keeps it
`C^∞` on `Q0`.  This is the `cos`-analogue of `Work.Blocks.smoothOpen_div_sin`. -/
theorem smoothOpen_div_cos {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / Real.cos θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := h
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn.of_le le_top
  exact h1.div h2 (fun p hp => by
    rcases p with ⟨z, θ⟩
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩))

end Work.FTS_EllLimOK.Pinning
