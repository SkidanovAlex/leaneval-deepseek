import Mathlib

set_option linter.unusedVariables false

namespace Work.RPB1a

/-- The map `z ↦ (z - z₀) * exp (L z / k)` has strict derivative `1` at `z₀`, whenever `L z₀ = 0`
and `L` is complex differentiable on a ball around `z₀`. The key point is that over `ℂ` a function
complex differentiable on an open set is analytic, hence `C^∞`, hence strictly differentiable. -/
theorem hasStrictDerivAt_self_mul_exp_div {L : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} {k : ℕ}
    (hr : 0 < r) (hk : k ≠ 0) (hL0 : L z₀ = 0) (hL : DifferentiableOn ℂ L (Metric.ball z₀ r)) :
    HasStrictDerivAt (fun z => (z - z₀) * Complex.exp (L z / k)) 1 z₀ := by
  have hz₀ : Metric.ball z₀ r ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hr
  -- `L` is complex differentiable on a neighbourhood of `z₀`, hence analytic there, hence `C^∞`.
  have hLan : AnalyticAt ℂ L z₀ := hL.analyticAt hz₀
  -- therefore `L` is strictly differentiable at `z₀`;
  have hLs : HasStrictDerivAt L (deriv L z₀) z₀ :=
    ContDiffAt.hasStrictDerivAt (hLan.contDiffAt (n := ⊤)) (by simp)
  -- the chain rule gives the strict derivative of `z ↦ exp (L z / k)`;
  have hΦs : HasStrictDerivAt (fun z => L z / (k : ℂ)) (deriv L z₀ / (k : ℂ)) z₀ :=
    hLs.div_const (k : ℂ)
  have hes : HasStrictDerivAt (fun z => Complex.exp (L z / (k : ℂ)))
      (Complex.exp (L z₀ / (k : ℂ)) * (deriv L z₀ / (k : ℂ))) z₀ :=
    hΦs.cexp
  -- and `z ↦ z - z₀` has strict derivative `1`;
  have hgs : HasStrictDerivAt (fun z => z - z₀) 1 z₀ := by
    have h : HasStrictDerivAt (fun z => z - z₀) (1 - 0) z₀ :=
      (hasStrictDerivAt_id z₀).sub (hasStrictDerivAt_const (x := z₀) z₀)
    simpa using h
  -- the product rule yields the claim, since the second factor vanishes at `z₀`.
  have hprods : HasStrictDerivAt (fun z => (z - z₀) * Complex.exp (L z / (k : ℂ)))
      (1 * Complex.exp (L z₀ / (k : ℂ)) +
        (z₀ - z₀) * (Complex.exp (L z₀ / (k : ℂ)) * (deriv L z₀ / (k : ℂ)))) z₀ :=
    hgs.mul hes
  simpa [hL0, Complex.exp_zero] using hprods

end Work.RPB1a
