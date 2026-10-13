/-
# The derivative of the angular factor `C0h`

`C0h θ = 3 K(θ) sin(2θ)` with `K(θ) = 3 sin θ cos²θ` (see `Submission.Work.Coercivity.C0Defs`),
so `C0h θ = 9 sin θ cos²θ sin(2θ)` and a direct computation gives

  `C0h'(θ) = 9 cos²θ (cos θ - 2 sin²θ) sin(2θ) + 18 sin θ cos²θ cos(2θ)
           = 18 sin θ cos²θ (2 cos²θ - 3 sin²θ) = C0g θ`.

The proof computes the derivative of `sin θ · cos²θ · sin(2θ)` with the product and chain
rules of `HasDerivAt`/`deriv`, then reduces the resulting trigonometric expression with
`sin(2θ) = 2 sin θ cos θ`, `cos(2θ) = 2 cos²θ - 1` and `sin²θ + cos²θ = 1`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Coercivity.C0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem C0h_deriv (θ : ℝ) : deriv Work.Coercivity.C0h θ = Work.Coercivity.C0g θ := by
  -- derivative of `sin (2 ·)`
  have hsin2 : deriv (fun t : ℝ => Real.sin (2 * t)) θ = Real.cos (2 * θ) * 2 := by
    rw [show (fun t : ℝ => Real.sin (2 * t)) = (Real.sin ∘ (fun t : ℝ => 2 * t)) from rfl]
    rw [deriv_comp θ (by fun_prop : DifferentiableAt ℝ Real.sin (2 * θ))
          (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => 2 * t) θ)]
    have h1 : deriv Real.sin (2 * θ) = Real.cos (2 * θ) := (Real.hasDerivAt_sin (2 * θ)).deriv
    have h2 : deriv (fun t : ℝ => 2 * t) θ = 2 := by
      rw [show (fun t : ℝ => 2 * t) = (fun y : ℝ => 2 * id y) from rfl]
      rw [((hasDerivAt_id θ).const_mul (2 : ℝ)).deriv]
      norm_num
    rw [h1, h2]
  -- derivative of `cos ^ 2`
  have hcos2 : deriv (fun t : ℝ => Real.cos t ^ 2) θ = 2 * Real.cos θ * (-Real.sin θ) := by
    rw [show (fun t : ℝ => Real.cos t ^ 2) = (Real.cos ^ 2) from rfl]
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.cos t) θ) 2]
    rw [Real.deriv_cos]
    ring
  -- derivative of the density `sin θ · cos²θ · sin(2θ)`
  have hF : deriv (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t)) θ
      = (Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * (2 * Real.cos θ * -Real.sin θ)) * Real.sin (2 * θ)
        + Real.sin θ * Real.cos θ ^ 2 * (Real.cos (2 * θ) * 2) := by
    rw [show (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t))
        = ((fun t : ℝ => Real.sin t * Real.cos t ^ 2) * (fun t : ℝ => Real.sin (2 * t))) from rfl]
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    rw [show (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
        = ((fun t : ℝ => Real.sin t) * (fun t : ℝ => Real.cos t ^ 2)) from rfl]
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    have h1 : deriv (fun t : ℝ => Real.sin t) θ = Real.cos θ := by
      rw [show (fun t : ℝ => Real.sin t) = Real.sin from rfl]
      exact (Real.hasDerivAt_sin θ).deriv
    rw [h1, hcos2, hsin2]
  -- unfold `C0h = 9 · (density)` and apply the computation
  rw [show C0h = (fun t : ℝ => 9 * (Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t))) from by
        funext t
        simp only [C0h, Spaces.K]
        ring]
  rw [deriv_const_mul (9 : ℝ)
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t)) θ)]
  rw [hF]
  -- the trigonometric bookkeeping
  simp only [C0g, Real.sin_two_mul, Real.cos_two_mul]
  ring_nf
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [show Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 from by ring]
  rw [hs]
  ring

end Work.Coercivity
