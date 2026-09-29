import Mathlib

namespace Work.TMLECore

open MeasureTheory

/-- For any complex polynomial `p`, the function `x ↦ log ‖p (exp (2π i x))‖` is interval
integrable on `[0,1]`. -/
theorem intervalIntegrable_log_poly_circle (p : Polynomial ℂ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖) volume (0 : ℝ) 1 := by
  -- A polynomial function is meromorphic on any set.
  have hmero : MeromorphicOn (fun z : ℂ => Polynomial.eval z p) (Metric.sphere 0 |(1 : ℝ)|) :=
    fun z _ => (AnalyticOnNhd.eval_polynomial p).meromorphicOn z (Set.mem_univ z)
  -- Hence `log ‖p ·‖` is circle integrable over the unit circle.
  have hcirc : CircleIntegrable (fun z : ℂ => Real.log ‖Polynomial.eval z p‖) 0 1 :=
    hmero.circleIntegrable_log_norm
  -- Circle integrability is interval integrability of `θ ↦ log ‖p (circleMap 0 1 θ)‖` on `[0, 2π]`.
  have hcirc' : IntervalIntegrable
      (fun θ : ℝ => Real.log ‖Polynomial.eval (circleMap 0 1 θ) p‖) volume 0 (2 * Real.pi) := hcirc
  -- Reparametrise `θ = 2π x` to get interval integrability on `[0,1]`.
  have h2 := hcirc'.comp_mul_left (c := 2 * Real.pi)
  rw [zero_div, div_self (by positivity : (2 * Real.pi) ≠ 0)] at h2
  -- Identify the two integrands.
  have hx : ∀ x : ℝ, circleMap 0 1 (2 * Real.pi * x) = Complex.exp (2 * Real.pi * Complex.I * x) := by
    intro x
    rw [circleMap, Complex.ofReal_one, one_mul, zero_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hfe : (fun x : ℝ => Real.log ‖Polynomial.eval (circleMap 0 1 (2 * Real.pi * x)) p‖)
      = (fun x : ℝ =>
          Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖) := by
    funext x
    rw [hx x]
  rw [hfe] at h2
  exact h2

end Work.TMLECore
