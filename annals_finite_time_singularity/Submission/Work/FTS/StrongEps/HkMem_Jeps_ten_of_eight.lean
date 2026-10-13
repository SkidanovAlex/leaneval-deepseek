import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/- **`J_ε : ℋ⁸ → ℋ¹⁰`** for every `ε > 0`: the two-order gain of the log-coordinate mollifier.

This is the `m = 2`, `k = 8` instance of the *scale-free* gain
`Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos`
(`Submission/Work/FTS/StrongEps/TenOfEight/GainAll.lean`), which removes the restriction
`ε ≤ 1` of `EpsE4Thr.HkMem_Jeps_gain` by replacing the routed density
`LamFull ρ ε c M` (whose domination of the routed kernel derivatives needs `ε⁻¹^{a+b} ≤ ε⁻¹^M`,
i.e. `ε ≤ 1`) by the scale-free density `LamAll ρ ε c M` with the kernel factor
`max 1 (ε⁻¹^M)`.  The boundary-vanishing hypothesis of that theorem is never used
(`J_ε f` only reads `f` on the open quadrant, and the gain is a pointwise estimate on
`(0,∞) × (0,π/2)`), so it is not needed here. -/
theorem HkMem_Jeps_ten_of_eight {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α 8 f) :
    Work.Spaces.HkMem α 10 (Jeps ρ ε f) :=
  Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 8 2 (by norm_num) ε hε f
    hsm hmem

end Work.FTS.StrongEps
