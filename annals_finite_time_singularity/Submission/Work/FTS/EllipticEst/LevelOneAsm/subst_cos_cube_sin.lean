import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LevelOneAsm

open MeasureTheory intervalIntegral

/-- Substitution `u = sin θ` on the angular interval `Iθ = [0, π/2]`:
`∫_0^{π/2} cos³θ · f(sin θ) dθ = ∫_0^1 (1 - u²) · f u du`.

The change of variables `u = sin θ` maps `[0, π/2]` onto `[0, 1]` with `du = cos θ dθ`,
and `cos³θ = cos θ · (1 - sin²θ)` on that interval. -/
theorem subst_cos_cube_sin (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ θ in Work.Spaces.Iθ, Real.cos θ ^ 3 * f (Real.sin θ)
      = ∫ u in (0:ℝ)..1, (1 - u ^ 2) * f u := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  set g : ℝ → ℝ := fun u => (1 - u ^ 2) * f u with hgdef
  have hgc : Continuous g := by
    rw [hgdef]
    exact (continuous_const.sub (continuous_id.pow 2)).mul hf
  -- change of variables `u = sin θ`, `du = cos θ dθ`
  have hcv := integral_comp_mul_deriv (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := Real.sin) (f' := Real.cos) (g := g)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hgc
  simp only [Function.comp_apply, Real.sin_zero, Real.sin_pi_div_two] at hcv
  -- rewrite the set integral over `Iθ = Icc 0 (π/2)` as the interval integral `0..π/2`
  have hIθ : ∫ θ in Work.Spaces.Iθ, Real.cos θ ^ 3 * f (Real.sin θ)
      = ∫ θ in (0 : ℝ)..Real.pi / 2, g (Real.sin θ) * Real.cos θ := by
    change ∫ θ in Set.Icc (0:ℝ) (Real.pi/2), Real.cos θ ^ 3 * f (Real.sin θ)
        = ∫ θ in (0 : ℝ)..Real.pi / 2, g (Real.sin θ) * Real.cos θ
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← integral_of_le hpi]
    apply integral_congr
    intro θ _
    simp only [hgdef]
    have hsq : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [show Real.cos θ ^ 3 = Real.cos θ ^ 2 * Real.cos θ from by ring, hsq]
    ring
  rw [hIθ, hcv, hgdef]

end Work.FTS.EllipticEst.LevelOneAsm
