import Mathlib
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Set Filter

namespace Commons.Analysis.ExpLog

/-- Change of variables `t = exp u` in the tail integral
`∫ t = x..∞, (log t)^10 / (t * √t) dt`, which becomes
`∫ u = log x..∞, u^10 * exp (-(u/2)) du`. -/
theorem integral_comp_exp_pow_log_sqrt {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t)) =
      (∫ u : ℝ in Set.Ioi (Real.log x), u ^ 10 * Real.exp (-(u / 2))) := by
  let g : ℝ → ℝ := fun t => (Real.log t) ^ 10 / (t * Real.sqrt t)
  -- One-dimensional change of variables with the injective differentiable map `exp`
  -- on `s = Ioi (log x)`, whose image is `Ioi x`.
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (Real.log x)) (f := Real.exp) (f' := fun u : ℝ => Real.exp u) (g := g)
    (hs := measurableSet_Ioi)
    (hf' := fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (hf := Real.exp_injective.injOn)
  -- Pointwise identity of the transformed integrand:
  -- `exp u * (u^10 / (exp u * √(exp u))) = u^10 * exp (-(u/2))`.
  have hpoint (u : ℝ) :
      Real.exp u * ((Real.log (Real.exp u)) ^ 10 / (Real.exp u * Real.sqrt (Real.exp u))) =
        u ^ 10 * Real.exp (-(u / 2)) := by
    rw [Real.log_exp]
    rw [← Real.exp_half u]
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  calc
    (∫ t : ℝ in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t)) =
        ∫ t : ℝ in Set.Ioi x, g t := by
      rfl
    _ = ∫ t : ℝ in Real.exp '' Set.Ioi (Real.log x), g t := by
      congr 1
      rw [Real.image_exp_Ioi, Real.exp_log hx]
    _ = ∫ u : ℝ in Set.Ioi (Real.log x), |Real.exp u| • g (Real.exp u) := hchange
    _ = ∫ u : ℝ in Set.Ioi (Real.log x), u ^ 10 * Real.exp (-(u / 2)) := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [g]
      have hpos : 0 < Real.exp u := Real.exp_pos u
      rw [abs_of_pos hpos]
      exact hpoint u

end Commons.Analysis.ExpLog
