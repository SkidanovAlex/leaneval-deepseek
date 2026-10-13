import Mathlib.Basic.Real.Basic
import Submission.Work.Elliptic.WtoHAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option linter.unusedVariables false

/-- `D_θ^i` of `g · f` equals `g · D_θ^i f` for the factor `g(z) = (z+1)³/z²`, which is
`(z+1)³ · divZ2 f` as a function of `(z,θ)`; the factor is constant in `θ`, so it pulls out
of `D_θ^i`. -/
theorem WtoH_Mixed_g_eq {f : ℝ → ℝ → ℝ} (i : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z θ
      = (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ := by
  rw [g_divZ2_eq, DthIter_const_mul]

end Work.Elliptic
