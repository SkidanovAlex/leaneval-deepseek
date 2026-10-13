import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- **The source `F` of the class `EllHyp` is `C^∞` on the open quadrant.**

`EllHyp α k F Ψ` contains `SmoothNbhd Ψ` (analyticity of `Ψ` on the neighbourhood
`(-1,∞) × (-1,π/2+1)` of the closed quadrant) and the elliptic law
`bslOp α Ψ = F` on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  The certificate
`Cert.SmoothOpen_bslOp` shows that `bslOp α Ψ` is `C^∞` on `Q0`, and `F` agrees with it
there, so `F` is `C^∞` on `Q0`.  (Note that `F` itself is *not* `SmoothNbhd` in general:
the term `∂_θ(tan θ · Ψ)` of `bslOp` has a pole at `θ = π/2`, which lies inside the
`SmoothNbhd` neighbourhood but outside the open quadrant.) -/
theorem EllHyp_F_smoothOpen (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  -- `bslOp α Ψ` is `C^∞` on the open quadrant
  have hbsl : SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Cert.SmoothOpen_bslOp_int α Ψ hHyp.smooth
  -- `F` agrees with `bslOp α Ψ` on the open quadrant (the elliptic law)
  have hF : SmoothOpen F :=
    Cert.smoothOpen_congr_bsl hbsl (fun z θ hz hθ0 hθ1 => hHyp.sol.1 z hz θ hθ0 hθ1)
  exact (smoothOpen_iff_forall F).mp hF n

end Work.FTS.EllipticEst
