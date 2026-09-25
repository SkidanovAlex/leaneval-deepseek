import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace Commons.Analysis.Fourier

/-- The convolution of an `L²` function with a measurable function is a.e.-strongly-measurable.

The integrand `(x, y) ↦ f y * k (x - y)` is jointly a.e.-strongly-measurable on the product
`ℝ × ℝ`, so by the Fubini measurability theorem its partial Bochner integral in `y` is
a.e.-strongly-measurable in `x`. Replacing `f` by a strongly measurable representative
(possible since `f ∈ L²`) makes the joint measurability immediate, and the two expressions
differ only on a null set, so they are a.e. equal. -/
theorem aestronglyMeasurable_conv {f : ℝ → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    {k : ℝ → ℂ} (hk : Measurable k) :
    MeasureTheory.AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, f y * k (x - y))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  -- a strongly measurable representative of `f`
  set g := hf.aestronglyMeasurable.mk f with hg
  have hg_sm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hg_eq : f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] g :=
    hf.aestronglyMeasurable.ae_eq_mk
  -- joint a.e.-strong-measurability of the integrand
  have hF : AEStronglyMeasurable (fun z : ℝ × ℝ => g z.2 * k (z.1 - z.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
    apply AEStronglyMeasurable.mul
    · exact hg_sm.comp_measurable measurable_snd |>.aestronglyMeasurable
    · exact (hk.comp measurable_sub).aestronglyMeasurable
  -- Fubini measurability of the partial integral
  have h_int := hF.integral_prod_right'
  -- the two integrals agree everywhere because `f` and `g` agree a.e.
  have hEq : (fun x : ℝ => ∫ y : ℝ, g y * k (x - y))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)]
        (fun x : ℝ => ∫ y : ℝ, f y * k (x - y)) := by
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards [hg_eq] with y hy
    rw [hy]
  exact h_int.congr hEq

end Commons.Analysis.Fourier