import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- Sharp Gaussian-type lower tail bound for a convex potential: if `V` is convex and
differentiable and `V'(x) < 0`, then `∫_{-∞}^x exp(-V(t)) dt ≤ exp(-V(x)) / (-V'(x))`. -/
theorem integral_Iic_exp_neg_le (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hVd : ∀ x, DifferentiableAt ℝ V x) {x : ℝ} (hx : deriv V x < 0) :
    ∫ t in Set.Iic x, Real.exp (-(V t)) ≤ Real.exp (-(V x)) / (-deriv V x) := by
  set a := deriv V x with ha_def
  have ha : a < 0 := by rw [ha_def]; exact hx
  -- pointwise exponential comparison coming from the tangent-line inequality at `x`
  have hpt : ∀ t ∈ Set.Iic x,
      Real.exp (-(V t)) ≤ Real.exp (-(V x) + a * x) * Real.exp ((-a) * t) := by
    intro t ht
    rcases lt_or_eq_of_le (show t ≤ x from ht) with htx | htx_eq
    · have hslope : (V x - V t) / (x - t) ≤ a := by
        have h := hV.slope_le_deriv (Set.mem_univ t) (Set.mem_univ x) htx (hVd x)
        rw [slope_def_field, ← ha_def] at h
        exact h
      have htx' : 0 < x - t := sub_pos.mpr htx
      have hkey : V x - V t ≤ a * (x - t) := (div_le_iff₀ htx').mp hslope
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [hkey])
    · rw [htx_eq]
      have heq : Real.exp (-(V x) + a * x) * Real.exp ((-a) * x) = Real.exp (-(V x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
  have hgint : IntegrableOn
      (fun t : ℝ => Real.exp (-(V x) + a * x) * Real.exp ((-a) * t)) (Set.Iic x) :=
    (integrableOn_exp_mul_Iic (a := -a) (by linarith) x).const_mul _
  have hval : ∫ t in Set.Iic x, Real.exp (-(V x) + a * x) * Real.exp ((-a) * t)
      = Real.exp (-(V x)) / (-a) := by
    rw [integral_const_mul, integral_exp_mul_Iic (a := -a) (by linarith) x]
    rw [← mul_div_assoc]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  calc ∫ t in Set.Iic x, Real.exp (-(V t))
      ≤ ∫ t in Set.Iic x, Real.exp (-(V x) + a * x) * Real.exp ((-a) * t) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun t => (Real.exp_pos _).le) hgint
          (by
            filter_upwards [self_mem_ae_restrict measurableSet_Iic] with t ht
            exact hpt t ht)
    _ = Real.exp (-(V x)) / (-a) := hval
    _ = Real.exp (-(V x)) / (-deriv V x) := by rw [ha_def]

end Commons.Analysis.Convex