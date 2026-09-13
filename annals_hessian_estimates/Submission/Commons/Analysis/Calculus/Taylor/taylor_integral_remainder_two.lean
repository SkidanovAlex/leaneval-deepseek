import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Taylor's theorem with integral remainder, order two

For a function `f : E → ℝ` on a real normed space `E` which is `C²` on the segment
`{x + t • y | t ∈ [0,1]}`, Taylor's formula with the integral form of the remainder reads

`f (x + y) = f x + Df(x)·y + ∫ t in 0..1, (1 - t) * D²f(x + t • y)[y, y]`.

This is the specialization `n = 1` of Mathlib's
`map_add_eq_sum_add_integral_iteratedFDeriv`, together with the identification of the
iterated derivatives with `fderiv` and `fderiv (fderiv f)`.
-/

namespace Commons.Analysis.Calculus.Taylor

open MeasureTheory intervalIntegral
open scoped Topology

theorem taylor_integral_remainder_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x y : E} (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 f (x + t • y)) :
    f (x + y) = f x + (fderiv ℝ f x) y
      + ∫ t in (0:ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y := by
  -- Taylor's theorem in integral form, specialized to `n = 1`.
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := y) (n := 1) hf
  rw [h]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, Nat.reduceAdd]
  -- Identify the integrand with `(1 - t) * D²f(x + t • y)[y, y]`.
  have hcongr : ∫ t in (0:ℝ)..1, (1 - t) • (iteratedFDeriv ℝ 2 f (x + t • y)) (fun _ => y)
      = ∫ t in (0:ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y := by
    apply intervalIntegral.integral_congr
    intro t _
    change (1 - t) • (iteratedFDeriv ℝ 2 f (x + t • y)) (fun _ => y)
      = (1 - t) * ((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y
    rw [iteratedFDeriv_two_apply]
    simp [smul_eq_mul]
  rw [hcongr]
  simp [Nat.factorial_zero, smul_eq_mul]

end Commons.Analysis.Calculus.Taylor
