import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.hasDerivAt_self_antideriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem HonSelfDeriv (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
          - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) θ := by
  intro θ hθ
  -- `u` is `C²` at any interior point, since it is `C^n` on the open interval for every `n`.
  have h2 : ContDiffAt ℝ 2 u θ := (hsm 2).contDiffAt (isOpen_Ioo.mem_nhds hθ)
  -- the pointwise antiderivative identity for the `θ`-slice, for `Work.Elliptic.Lzero`.
  have h := Work.FTS.EllipticEst.hasDerivAt_self_antideriv u θ hθ h2
  -- identify `Lzero` on the constant `θ`-slice with the one-dimensional operator `Lzero1`.
  have hL : Work.Elliptic.Lzero (fun _ s => u s) 0 θ = Work.FTS.EllipticEst.Lzero1 u θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0]
  exact h.congr_deriv (by rw [hL])

end Work.FTS.EllipticEst.Honest
