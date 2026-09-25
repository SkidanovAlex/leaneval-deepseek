import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory.Integral

/-- Double window average identity: for a nonnegative measurable `F : ℝ → ℝ≥0∞` and `0 ≤ h`,
the iterated integral of `F (x + t + s)` over `t, s ∈ (0, h]` and `x ∈ ℝ` equals
`h * (h * ∫ F)`. The outer integral over `x` makes the expression translation invariant,
so the two window integrals simply contribute the volume `h` each. -/
theorem double_window_comp_add_add {h : ℝ} (hh : 0 ≤ h) {F : ℝ → ENNReal} (hF : Measurable F) :
    ∫⁻ x, ∫⁻ t in Set.Ioc (0:ℝ) h, ∫⁻ s in Set.Ioc (0:ℝ) h, F (x + t + s)
      = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) := by
  set I : Set ℝ := Set.Ioc (0:ℝ) h with hIeq
  have hIvol : volume I = ENNReal.ofReal h := by
    rw [hIeq, Real.volume_Ioc, sub_zero]
  have hconst : ∀ c : ℝ≥0∞, ∫⁻ t in I, c = ENNReal.ofReal h * c := by
    intro c
    rw [lintegral_const, Measure.restrict_apply_univ, hIvol, mul_comm]
  -- Translation invariance of the outer integral in `x`.
  have htrans : ∀ t s : ℝ, ∫⁻ x, F (x + t + s) = ∫⁻ x, F x := by
    intro t s
    have := lintegral_add_right_eq_self (μ := volume) F (t + s)
    simpa only [add_assoc] using this
  -- Swap the `x`-integral with the `t`-integral.
  have hstep1 : ∫⁻ x, ∫⁻ t in I, ∫⁻ s in I, F (x + t + s)
      = ∫⁻ t in I, ∫⁻ x, ∫⁻ s in I, F (x + t + s) := by
    refine lintegral_lintegral_swap (f := fun x t : ℝ => ∫⁻ s in I, F (x + t + s)) ?_
    have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => F (q.1.1 + q.1.2 + q.2)) :=
      hF.comp (by fun_prop)
    have hmeas := Measurable.lintegral_prod_right (ν := volume.restrict I)
      (f := fun p : ℝ × ℝ => fun s : ℝ => F (p.1 + p.2 + s)) hm
    exact hmeas.aemeasurable
  -- Swap the `x`-integral with the `s`-integral (for fixed `t`).
  have hstep2 : ∫⁻ t in I, ∫⁻ x, ∫⁻ s in I, F (x + t + s)
      = ∫⁻ t in I, ∫⁻ s in I, ∫⁻ x, F (x + t + s) := by
    apply lintegral_congr; intro t
    refine lintegral_lintegral_swap (f := fun x s : ℝ => F (x + t + s)) ?_
    exact (hF.comp (by fun_prop)).aemeasurable
  -- Translation invariance pointwise in `t` and `s`.
  have hstep3 : ∫⁻ t in I, ∫⁻ s in I, ∫⁻ x, F (x + t + s)
      = ∫⁻ t in I, ∫⁻ s in I, ∫⁻ x, F x := by
    apply lintegral_congr; intro t
    apply lintegral_congr; intro s
    exact htrans t s
  -- The remaining integrals are constants.
  have hstep4 : ∫⁻ t in I, ∫⁻ s in I, ∫⁻ x, F x
      = ENNReal.ofReal h * (ENNReal.ofReal h * ∫⁻ x, F x) := by
    rw [hconst (∫⁻ x, F x), hconst (ENNReal.ofReal h * ∫⁻ x, F x)]
  rw [hstep1, hstep2, hstep3, hstep4]

end Commons.MeasureTheory.Integral