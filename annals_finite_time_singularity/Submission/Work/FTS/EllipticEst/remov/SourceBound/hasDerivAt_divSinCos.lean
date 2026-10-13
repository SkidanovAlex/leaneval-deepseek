import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem hasDerivAt_divSinCos {u G : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContDiffAt ℝ 2 u x)
    (hG : G x = -(deriv u x) * Work.Elliptic.sinCos2 x + u x * (Real.cos x * Real.cos (2 * x))) :
    HasDerivAt (fun θ => u θ / (Real.sin θ * Real.cos θ))
      (-(G x) / (Real.sin x ^ 2 * Real.cos x ^ 3)) x := by
  -- On `(0, π/2)` both `sin x` and `cos x` are positive, hence non-zero.
  have hsin : Real.sin x ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])).ne'
  have hcos : Real.cos x ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩).ne'
  -- Derivative of the denominator `sin θ * cos θ`, equal to `cos (2x)`.
  have hsc : HasDerivAt (fun θ : ℝ => Real.sin θ * Real.cos θ)
      (Real.cos x ^ 2 - Real.sin x ^ 2) x := by
    have h := (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)
    convert h using 1
    ring
  have hd : HasDerivAt u (deriv u x) x := (hu.differentiableAt (by norm_num)).hasDerivAt
  have h := hd.div hsc (mul_ne_zero hsin hcos)
  convert h using 1
  -- `G x = -(deriv u x) * sin x * cos²x + u x * cos x * cos (2x)`, and
  -- `cos (2x) = cos²x - sin²x`; the two sides differ by the factor `cos x` in
  -- `G`, which cancels against the extra `cos x` in the denominator.
  rw [hG, Work.Elliptic.sinCos2, Real.cos_two_mul']
  field_simp
  ring

end Work.FTS.EllipticEst.remov.SourceBound
