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

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **Pointwise antiderivative identity for the self-pairing of `Lzero1`.**  For `u : ℝ → ℝ`
which is `C²` at `θ ∈ (0, π/2)`, the function `s ↦ -(deriv u s) * u s + (1/2) * tan s * (u s)^2`
has derivative `Lzero1 u θ * u θ - (deriv u θ)^2 - (1/2) * (u θ / cos θ)^2 + 6 * (u θ)^2` at `θ`.

This is a two-line wrapper: apply the already-proved
`Work.FTS.EllipticEst.hasDerivAt_self_antideriv` (in
`Submission/Work/FTS/EllipticEst/hasDerivAt_self_antideriv.lean`), which gives the same
`HasDerivAt` with `Work.Elliptic.Lzero (fun _ s => u s) 0 θ` in place of `Lzero1 u θ`, and
rewrite with `Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0 θ` (in
`Submission/Work/FTS/EllipticEst/StraightDefs.lean`).

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceAntiderivDeriv`. -/
theorem SliceAntiderivDeriv (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (h2 : ContDiffAt ℝ 2 u θ) :
    HasDerivAt (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
      (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
        - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) θ := by
  -- The already-proved `L₀`-version of the identity, at `z = 0`.
  have h := Work.FTS.EllipticEst.hasDerivAt_self_antideriv u θ hθ h2
  -- `Lzero1` is the `θ`-slice of `Work.Elliptic.Lzero`, so the derivative values agree.
  have hL : Work.Elliptic.Lzero (fun _ s => u s) 0 θ = Work.FTS.EllipticEst.Lzero1 u θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0]
  exact h.congr_deriv (by rw [hL])

end Work.FTS.EllipticEst.Honest.SelfAux
