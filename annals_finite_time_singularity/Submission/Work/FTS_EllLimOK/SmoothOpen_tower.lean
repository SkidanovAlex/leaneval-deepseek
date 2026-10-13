import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem SmoothOpen_tower {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d G z' θ)
          (Work.Spaces.mixed (c + 1) d G z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d G z θ')
          (Work.Spaces.mixed c (d + 1) G z θ / Real.sin (2 * θ)) θ) := by
  have hpp := fun (c d : ℕ) =>
    Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d hG
  constructor
  · -- the radial tower `∂_z (D_z^c D_θ^d G) = D_z^{c+1} D_θ^d G / z`
    intro c d _ z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hd := (hG.mixed c d).hasDerivAt_slice (θ := θ) ⟨hθ0, hθ1⟩ hz
    rwa [(hpp c d).1 z θ hzθ] at hd
  · -- the angular tower `∂_θ (D_z^c D_θ^d G) = D_z^c D_θ^{d+1} G / sin 2θ`
    intro c d _ z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hd : HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d G z θ')
        (Work.Spaces.pth (Work.Spaces.mixed c d G) z θ) θ :=
      (((hG.mixed c d).curry_θ hz).contDiffAt
          (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)).differentiableAt (by simp) |>.hasDerivAt
    rwa [(hpp c d).2.1 z θ hzθ] at hd

end Work.FTS_EllLimOK
