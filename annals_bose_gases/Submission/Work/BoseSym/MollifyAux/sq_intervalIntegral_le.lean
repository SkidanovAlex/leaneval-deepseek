import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.MollifyAux

open MeasureTheory
open scoped Interval

/-- Cauchy–Schwarz for the Lebesgue integral over `[0,1]`: the square of the integral of `g` is
dominated by the integral of `g ^ 2`.

Proof: the variance identity.  With `c = ∫₀¹ g`, the integral `∫₀¹ (g t - c)^2` is nonnegative;
expanding the square and integrating term by term gives `∫₀¹ (g t - c)^2 = (∫₀¹ g t ^ 2) - c ^ 2`,
whence `c ^ 2 ≤ ∫₀¹ g t ^ 2`. -/
theorem sq_intervalIntegral_le {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t in (0:ℝ)..1, g t) ^ 2 ≤ ∫ t in (0:ℝ)..1, (g t) ^ 2 := by
  set c : ℝ := ∫ t in (0:ℝ)..1, g t with hc
  have hnn : 0 ≤ ∫ t in (0:ℝ)..1, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have h1 : IntervalIntegrable (fun t => (g t) ^ 2) volume 0 1 :=
    (hg.pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => (2 * c) * g t) volume 0 1 :=
    (hg.const_mul (2 * c)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t => c ^ 2) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hcongr : ∫ t in (0:ℝ)..1, (g t - c) ^ 2
      = ∫ t in (0:ℝ)..1, ((g t) ^ 2 - (2 * c) * g t + c ^ 2) :=
    intervalIntegral.integral_congr (fun t _ => by ring)
  have hkey : ∫ t in (0:ℝ)..1, (g t - c) ^ 2 = (∫ t in (0:ℝ)..1, (g t) ^ 2) - c ^ 2 := by
    rw [hcongr, intervalIntegral.integral_add (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    norm_num
    ring
  rw [hkey] at hnn
  linarith [hnn, hc]

end Work.BoseSym.MollifyAux
