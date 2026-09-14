import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- Sharp Gaussian-type tail bound for a convex potential: if `V` is convex and differentiable
and `V'(x) > 0`, then `∫_x^∞ exp(-V(t)) dt ≤ exp(-V(x)) / V'(x)`. -/
theorem integral_Ioi_exp_neg_le (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hVd : ∀ x, DifferentiableAt ℝ V x) {x : ℝ} (hx : 0 < deriv V x) :
    ∫ t in Set.Ioi x, Real.exp (-(V t)) ≤ Real.exp (-(V x)) / deriv V x := by
  set a := deriv V x with ha_def
  have ha : 0 < a := by rw [ha_def]; exact hx
  -- pointwise exponential comparison coming from the tangent-line inequality
  have hpt : ∀ t ∈ Set.Ioi x,
      Real.exp (-(V t)) ≤ Real.exp (-(V x) + a * x) * Real.exp ((-a) * t) := by
    intro t ht
    have hxt : x < t := ht
    have hslope : a ≤ (V t - V x) / (t - x) := by
      have h := hV.deriv_le_slope (Set.mem_univ x) (Set.mem_univ t) hxt (hVd x)
      rw [slope_def_field] at h
      rw [← ha_def] at h
      exact h
    have htx : 0 < t - x := sub_pos.mpr hxt
    have hkey : a * (t - x) ≤ V t - V x := (le_div_iff₀ htx).mp hslope
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hgint : IntegrableOn (fun t : ℝ => Real.exp (-(V x) + a * x) * Real.exp ((-a) * t))
      (Set.Ioi x) :=
    (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  have hval : ∫ t in Set.Ioi x, Real.exp (-(V x) + a * x) * Real.exp ((-a) * t)
      = Real.exp (-(V x)) / a := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x]
    rw [show -Real.exp ((-a) * x) / -a = Real.exp (-(a * x)) / a by
      rw [neg_div_neg_eq, neg_mul]]
    rw [← mul_div_assoc,
      show Real.exp (-(V x) + a * x) * Real.exp (-(a * x)) = Real.exp (-(V x)) by
        rw [← Real.exp_add]; congr 1; ring]
  calc ∫ t in Set.Ioi x, Real.exp (-(V t))
      ≤ ∫ t in Set.Ioi x, Real.exp (-(V x) + a * x) * Real.exp ((-a) * t) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun t => (Real.exp_pos _).le) hgint
          (by
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            exact hpt t ht)
    _ = Real.exp (-(V x)) / a := hval

end Commons.Analysis.Convex