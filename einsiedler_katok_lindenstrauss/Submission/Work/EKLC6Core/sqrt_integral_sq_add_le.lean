import Mathlib

namespace Work.EKLC6Core

open MeasureTheory

/-- For a real-valued function `f` in `L²(ν)`, the square root of the integral of `f²`
coincides with the real `L²` seminorm `lpNorm f 2 ν`. -/
lemma sqrt_integral_sq_eq_lpNorm {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 ν) :
    Real.sqrt (∫ x, (f x)^2 ∂ν) = MeasureTheory.lpNorm f 2 ν := by
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow]
  have hfun : (fun x => ‖f x‖ ^ (2 : ℝ)) = fun x => (f x)^2 := by
    funext x
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [hfun, one_div]

theorem sqrt_integral_sq_add_le {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) (a b : X → ℝ)
    (ha : MeasureTheory.MemLp a 2 ν) (hb : MeasureTheory.MemLp b 2 ν) :
    Real.sqrt (∫ x, (a x + b x)^2 ∂ν)
      ≤ Real.sqrt (∫ x, (a x)^2 ∂ν) + Real.sqrt (∫ x, (b x)^2 ∂ν) := by
  change Real.sqrt (∫ x, ((a + b) x)^2 ∂ν)
      ≤ Real.sqrt (∫ x, (a x)^2 ∂ν) + Real.sqrt (∫ x, (b x)^2 ∂ν)
  rw [sqrt_integral_sq_eq_lpNorm ν (a + b) (ha.add hb),
      sqrt_integral_sq_eq_lpNorm ν a ha, sqrt_integral_sq_eq_lpNorm ν b hb]
  exact MeasureTheory.lpNorm_add_le ha (by norm_num)

end Work.EKLC6Core
