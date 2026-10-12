import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Minimiser

/-- The `L²` pairing of the multiplication of `u` by an `L∞` class `F` against `v`
is the integral of the pointwise product `F · u · v`.

This is `MeasureTheory.L2.inner_def` combined with the almost-everywhere description
of the `L∞`-scalar multiplication on `Lp` (`MeasureTheory.Lp.coeFn_lpSMul`). -/
theorem inner_lpSMul {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (F : MeasureTheory.Lp ℝ (⊤ : ENNReal) μ) (u v : MeasureTheory.Lp ℝ 2 μ) :
    inner ℝ (F • u) v = ∫ x, (F : α → ℝ) x * (u : α → ℝ) x * (v : α → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  simp only [Real.inner_apply]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) F u] with x hx
  simp only [hx, Pi.smul_apply', smul_eq_mul]

end Work.BoseSym.Minimiser
