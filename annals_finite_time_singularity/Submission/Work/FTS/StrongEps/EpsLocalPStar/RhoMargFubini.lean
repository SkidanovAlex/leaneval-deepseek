import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem RhoMargFubini {ρ : ℝ × ℝ → ℝ} {ε z : ℝ} (hε : 0 < ε) {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1))))) :
    ∫ q : ℝ × ℝ, ρ q * lam (z * Real.exp (-(ε * q.1)))
      = ∫ s, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s))) := by
  -- (The sign of `ε` is irrelevant here; record the hypothesis so the binding is used.)
  have _hε : (0 : ℝ) < ε := hε
  -- The measure on `ℝ × ℝ` is the product of the two Lebesgue measures.
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  -- Fubini for the Bochner integral (the integrand is given as integrable).
  rw [MeasureTheory.integral_prod
    (fun q : ℝ × ℝ => ρ q * lam (z * Real.exp (-(ε * q.1)))) hint]
  -- In the inner integral the factor `lam (z * exp (-(ε * s)))` is a constant, so it
  -- can be pulled out; the equality holds pointwise (hence a.e.).
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  exact MeasureTheory.integral_mul_const (lam (z * Real.exp (-(ε * s)))) (fun t => ρ (s, t))

end Work.FTS.StrongEps.EpsLocalPStar
