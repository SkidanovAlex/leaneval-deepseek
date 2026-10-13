import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.CutoffPieces

/-- For a function of class `SmoothInt`, every `θ`-slice over the open quadrant is
differentiable: `SmoothInt` gives joint `C^∞` differentiability of `uncurry v` at
`(z, θ)` for `z ∈ (-1, ∞)`, `θ ∈ (0, π/2)`, hence the `θ`-slice `θ' ↦ v z θ'` is
`C^∞` (in particular differentiable) at `θ` as soon as `z > 0`. -/
theorem SmoothIntSliceDifferentiableAt (v : ℝ → ℝ → ℝ) (h : Work.Spaces.SmoothInt v)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => v z θ') θ := by
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := by
    rw [Set.mem_Ioi]; linarith
  have hcd : ContDiffOn ℝ ⊤ (fun θ' => v z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h.contDiffOn_theta_slice hz'
  exact (hcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)

end Work.FTS.EllipticEst.Mine.CutoffPieces
