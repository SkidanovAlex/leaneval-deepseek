import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory
open scoped RealInnerProductSpace

/-- Cauchy–Schwarz (Bunyakovsky) inequality for the Lebesgue integral over a set, in the special
case of exponent `2`: for real functions `u`, `v` that are square-integrable on `s`,
`(∫_s u v)^2 ≤ (∫_s u^2) * (∫_s v^2)`.

The proof passes to the `L²` space `Lp ℝ 2 (volume.restrict s)`, which is an inner product space
whose inner product is the integral of the pointwise inner product, and applies the abstract
Cauchy–Schwarz inequality `real_inner_mul_inner_self_le` there, then transfers the four integrals
back along the `MemLp.toLp` a.e.-equalities. -/
theorem cs_integral {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict s)) :
    (∫ x in s, u x * v x) ^ 2 ≤ (∫ x in s, u x ^ 2) * (∫ x in s, v x ^ 2) := by
  have hB : (∫ x in s, u x * v x) = ∫ a in s, (hu.toLp u) a * (hv.toLp v) a :=
    integral_congr_ae (by
      filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
      rw [hx, hy])
  have hA : (∫ x in s, u x ^ 2) = ∫ a in s, (hu.toLp u) a * (hu.toLp u) a :=
    integral_congr_ae (by
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx, sq])
  have hC : (∫ x in s, v x ^ 2) = ∫ a in s, (hv.toLp v) a * (hv.toLp v) a :=
    integral_congr_ae (by
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx, sq])
  have h := real_inner_mul_inner_self_le (hu.toLp u) (hv.toLp v)
  simp only [L2.inner_def, Real.inner_apply] at h
  rw [hB, hA, hC]
  simpa [sq] using h

end Work.Spaces
