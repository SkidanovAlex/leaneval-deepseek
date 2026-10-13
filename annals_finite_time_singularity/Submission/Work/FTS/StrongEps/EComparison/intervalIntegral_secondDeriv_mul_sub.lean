import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- **Second-order Taylor formula with a vanishing lower end.**

If `ρ` is `C³` on `ℝ` and vanishes in a neighbourhood of `a`, then the triangular weighted
second derivative of `ρ` integrates back to `ρ z`:
```
∫_a^z ρ''(t) (z - t) dt = ρ z .
```
This is the fundamental theorem of calculus applied to the primitive `F t = ρ'(t)(z-t) + ρ(t)`,
whose derivative is exactly `ρ''(t)(z-t)`: the two extra terms `-ρ'(t) + ρ'(t)` cancel.  The
boundary terms at `a` vanish because `ρ` is identically zero near `a`, hence so are `ρ a` and
`ρ' a`; the boundary term at `z` vanishes because of the factor `(z - t)`. -/
theorem intervalIntegral_secondDeriv_mul_sub {a z : ℝ} {ρ : ℝ → ℝ} (haz : a ≤ z)
    (hρ : ContDiff ℝ 3 ρ) (hρa : ρ =ᶠ[nhds a] 0) :
    (∫ t in a..z, deriv (deriv ρ) t * (z - t)) = ρ z := by
  -- The proof actually works for every `a`, `z` (`Set.uIcc` is symmetric); the hypothesis
  -- `haz` is kept only because the statement was requested in this form.
  have haz' : a ≤ z := haz
  -- `ρ` and its first derivative vanish at `a`.
  have hρa0 : ρ a = 0 := by simpa using hρa.eq_of_nhds
  have hdρa0 : deriv ρ a = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hρa]
    simp
  -- Smoothness of `ρ`, `ρ'` and `ρ''`.
  have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by norm_num)
  have hdρ_diff : Differentiable ℝ (deriv ρ) := ContDiff.differentiable_deriv_two hρ2
  have hρ_diff : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv ρ) := hρ2.deriv'
  have h2d : Continuous (deriv (deriv ρ)) := hd1.continuous_deriv (by norm_num)
  -- The primitive `F t = ρ'(t)(z-t) + ρ(t)` has derivative `ρ''(t)(z-t)`.
  have hderiv : ∀ x ∈ Set.uIcc a z,
      HasDerivAt ((deriv ρ) * (fun t => z - t) + ρ) (deriv (deriv ρ) x * (z - x)) x := by
    intro x _
    have hx' := (((hdρ_diff x).hasDerivAt).mul ((hasDerivAt_id x).const_sub z)).add
      ((hρ_diff x).hasDerivAt)
    have hv : deriv (deriv ρ) x * (z - x) + deriv ρ x * (-1) + deriv ρ x
        = deriv (deriv ρ) x * (z - x) := by ring
    simpa [hv] using hx'
  -- The integrand is continuous, hence interval integrable.
  have hint : IntervalIntegrable (fun t => deriv (deriv ρ) t * (z - t)) volume a z :=
    (h2d.mul (continuous_const.sub continuous_id)).intervalIntegrable a z
  -- Fundamental theorem of calculus, then evaluate the boundary terms.
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc ∫ t in a..z, deriv (deriv ρ) t * (z - t)
      = ((deriv ρ) * (fun t => z - t) + ρ) z - ((deriv ρ) * (fun t => z - t) + ρ) a := hmain
    _ = ρ z := by simp only [Pi.add_apply, Pi.mul_apply]; rw [hρa0, hdρa0]; ring

end Work.FTS.StrongEps.EComparison
