import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set

/-- If `u` is differentiable on the open interval `(0, π/2)` with derivative `g`, then both
`u` and `g` are almost everywhere strongly measurable for Lebesgue measure restricted to the
closed interval `[0, π/2]`.

* For `u`: `h` gives `ContinuousOn u (Ioo 0 (π/2))`, hence a.e. strong measurability for
  `volume.restrict (Ioo 0 (π/2))`; the endpoints are null, so
  `MeasureTheory.restrict_Ioo_eq_restrict_Icc` transfers this to `Icc 0 (π/2)`.
* For `g`: on `(0, π/2)` the hypothesis says `g = deriv u` (`HasDerivAt.deriv`), and `deriv u`
  is strongly measurable (`stronglyMeasurable_deriv`); again transfer the restriction. -/
theorem AesmSlices {u g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt u (g θ) θ) :
    MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) ∧
      MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  -- The closed interval agrees, up to a null set, with the open one.
  have hIoo : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)) :=
    MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2)
  -- `u` is continuous on the open interval.
  have hcont : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (h θ hθ).continuousAt.continuousWithinAt
  constructor
  · rw [← hIoo]
    exact hcont.aestronglyMeasurable isOpen_Ioo.measurableSet
  · rw [← hIoo]
    -- On the open interval, `g` coincides with the (strongly measurable) derivative of `u`.
    refine (aestronglyMeasurable_deriv u
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem isOpen_Ioo.measurableSet] with θ hθ
    exact (h θ hθ).deriv

end Work.FTS.H2
