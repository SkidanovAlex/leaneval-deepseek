import Mathlib
import Submission.Work.MotK.TwAmbh

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

/-- The first component of the twisted inverse link map `R`, evaluated at the affine chart point
`(0, x₀, x₁, x₂, 1)` of the hyperplane `{v₀ = 0}`, does not vanish: expanding `kleinTwR0` at the
chart gives

  `-a b³ h x₂² - a b³ h² x₀ x₁² + a³ b h x₁ + a³ b h² x₀² x₂`,

whose `x₁`-coefficient is `a³ b h ≠ 0` (equivalently, evaluating at `(x₀,x₁,x₂) = (0,1,0)`
yields `a³ b h ≠ 0`). -/
theorem KleinTwRChart0 {K : Type*} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (Work.MotK.chart3 K) 0 ≠ 0 := by
  intro hzero
  have hφ : MvPolynomial.eval (fun i : Fin 3 => if i = (1 : Fin 3) then (1 : K) else 0)
      (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.chart3 K) 0) = a ^ 3 * b * h := by
    simp only [Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.chart3]
    simp
  rw [hzero, map_zero] at hφ
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 ha) hb) hh) hφ.symm

end Work.MotK.TGen
