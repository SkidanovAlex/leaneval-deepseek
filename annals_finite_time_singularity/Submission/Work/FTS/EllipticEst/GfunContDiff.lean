import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.LopIterSinSqDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Helper: `θ ↦ Real.cos (2 * θ)` is smooth. -/
theorem contDiff_cos_two : ContDiff ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ)) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

/-- Helper: `θ ↦ Real.sin (2 * θ)` is smooth. -/
theorem contDiff_sin_two : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

/-- Helper: the function `θ ↦ c * Real.cos (2 * θ)` is smooth. -/
theorem contDiff_const_mul_cos_two (c : ℝ) :
    ContDiff ℝ ⊤ (fun θ : ℝ => c * Real.cos (2 * θ)) :=
  contDiff_const.mul contDiff_cos_two

/-- Every coefficient `gfun n` of the recursion `gfun 0 = 1`,
`gfun (n+1) θ = 4 cos(2θ) gfun n θ + sin(2θ) (gfun n)'(θ)` is smooth on `ℝ`. -/
theorem GfunContDiff (n : ℕ) : ContDiff ℝ ⊤ (Work.FTS.EllipticEst.gfun n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
      rw [gfun_succ]
      have hd : ContDiff ℝ ⊤ (deriv (gfun n)) := ContDiff.deriv' ih
      exact ContDiff.add ((contDiff_const_mul_cos_two 4).mul ih) (contDiff_sin_two.mul hd)

end Work.FTS.EllipticEst
