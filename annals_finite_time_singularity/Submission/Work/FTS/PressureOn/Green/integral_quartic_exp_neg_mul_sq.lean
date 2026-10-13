import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green

/-- Antiderivative of `(4 s ^ 4 * a - 6 * s ^ 2) * exp (-(s ^ 2 * a))`:
`-2 * s ^ 3 * exp (-(s ^ 2 * a))`. -/
theorem hasDerivAt_quartic_exp_neg_mul_sq (a : ℝ) :
    ∀ s : ℝ, HasDerivAt (fun s : ℝ => -2 * s ^ 3 * Real.exp (-(s ^ 2 * a)))
      ((4 * s ^ 4 * a - 6 * s ^ 2) * Real.exp (-(s ^ 2 * a))) s := by
  intro s
  have hquad : HasDerivAt (fun s : ℝ => s ^ 2 * a) (2 * s * a) s := by
    simpa using (hasDerivAt_pow 2 s).mul_const a
  have hneg : HasDerivAt (fun s : ℝ => -(s ^ 2 * a)) (-(2 * s * a)) s := hquad.neg
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s ^ 2 * a)))
      (Real.exp (-(s ^ 2 * a)) * -(2 * s * a)) s := hneg.exp
  have hcub : HasDerivAt (fun s : ℝ => -2 * s ^ 3) (-2 * (3 * s ^ 2)) s := by
    simpa using (hasDerivAt_pow 3 s).const_mul (-2)
  refine (hcub.mul hexp).congr_deriv ?_
  ring

theorem integral_quartic_exp_neg_mul_sq (T a : ℝ) :
    ∫ s in (0 : ℝ)..T, (4 * s ^ 4 * a - 6 * s ^ 2) * Real.exp (-(s ^ 2 * a))
      = -2 * T ^ 3 * Real.exp (-(T ^ 2 * a)) := by
  have hInt : IntervalIntegrable
      (fun s : ℝ => (4 * s ^ 4 * a - 6 * s ^ 2) * Real.exp (-(s ^ 2 * a)))
      MeasureTheory.volume 0 T :=
    (by fun_prop : Continuous
      fun s : ℝ => (4 * s ^ 4 * a - 6 * s ^ 2) * Real.exp (-(s ^ 2 * a))).intervalIntegrable 0 T
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_quartic_exp_neg_mul_sq a x) hInt]
  simp

end Work.FTS.PressureOn.Green
