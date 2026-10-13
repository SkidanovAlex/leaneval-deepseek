import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

-- `hθ` is part of the requested signature but is not needed by the proof.
set_option linter.unusedVariables false in
/-- **An angular derivative divisible by `sin 2θ` costs nothing against the mixed weight.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/angular_sq_mul_Wt_sq_le.lean`,
namespace `Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le`.
If `d² ≤ K · sin(2θ)²` at `θ ∈ (0,π/2)` and `K ≥ 0`, then for arbitrary `u, α, z`
`(d·u)² · Wt(α,z,θ)² ≤ K · (u · Wt(α,z,θ))²`,
where `Wt α z θ = Work.Spaces.w z · sin(2θ)^{-γ/2}`, `γ = 1 + α/10`
(`Submission/Work/Spaces/Defs.lean`).  Indeed `sin(2θ)² ≤ 1`, so `hd` gives `d² ≤ K`; multiply by
the nonnegative factor `u² · Wt²`.  No hypothesis on `α` is needed (`hθ` is only cosmetic). -/
theorem angular_sq_mul_Wt_sq_le {K d u α z θ : ℝ} (hK : 0 ≤ K)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hd : d ^ 2 ≤ K * (Real.sin (2 * θ)) ^ 2) :
    (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ K * (u * Work.Spaces.Wt α z θ) ^ 2 := by
  have hsin : (Real.sin (2 * θ)) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hdK : d ^ 2 ≤ K := by nlinarith [hK, hsin]
  have hmain : d ^ 2 * u ^ 2 ≤ K * u ^ 2 :=
    mul_le_mul_of_nonneg_right hdK (sq_nonneg u)
  have hW : 0 ≤ (Work.Spaces.Wt α z θ) ^ 2 := sq_nonneg _
  calc (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = d ^ 2 * u ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ K * u ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmain hW
    _ = K * (u * Work.Spaces.Wt α z θ) ^ 2 := by ring

end Work.FTS.EllipticEst.Blocks
