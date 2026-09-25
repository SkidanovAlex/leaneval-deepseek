import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- For an integrable `g` on `ℝ` and reals `u ≤ v`, the Bochner set integral of `g` over
`Set.Ioc u v` is the difference of the primitive `t ↦ ∫ y in (0:ℝ)..t, g y` evaluated at `v`
and at `u`. -/
theorem intervalIntegral_Ioc_eq_primitive_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} (hg : Integrable g (volume : Measure ℝ)) {u v : ℝ}
    (huv : u ≤ v) :
    (∫ y in Set.Ioc u v, g y) = (∫ y in (0:ℝ)..v, g y) - (∫ y in (0:ℝ)..u, g y) := by
  rw [← intervalIntegral.integral_of_le huv]
  exact (intervalIntegral.integral_interval_sub_left
    (hg.intervalIntegrable : IntervalIntegrable g volume (0:ℝ) v)
    (hg.intervalIntegrable : IntervalIntegrable g volume (0:ℝ) u)).symm

/-- For fixed `x` and an integrable `g`, the function of `θ` given by the integral of `g` over the
dyadic grid cell of mesh `2 ^ (-k)` anchored at `x` (the cell `Ioc` starting at the grid point
`θ + ⌊(x - θ) * 2 ^ k⌋ * 2 ^ (-k)`) is a.e. measurable. -/
theorem aemeasurable_grid_cell_integral_fixed_x (k : ℤ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    AEMeasurable (fun θ : ℝ => ∫ y in Set.Ioc
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hc : (0:ℝ) < (2:ℝ)^(-k) := zpow_pos (by norm_num) (-k)
  -- the primitive `t ↦ ∫ y in 0..t, g y` is continuous (hence measurable)
  have hQcont : Continuous (fun t : ℝ => ∫ y in (0:ℝ)..t, g y) := hg.continuous_primitive 0
  -- the left grid endpoint is measurable in `θ`
  have hL : Measurable (fun θ : ℝ => θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k)) := by
    have hfloor : Measurable (fun θ : ℝ => (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ)) :=
      ((continuous_of_discreteTopology : Continuous (Int.cast : ℤ → ℝ)).measurable).comp
        (Int.measurable_floor.comp ((measurable_const.sub measurable_id).mul measurable_const))
    exact measurable_id.add (hfloor.mul measurable_const)
  -- rewrite the cell integral as a difference of the primitive at the two endpoints
  have h_eq : (fun θ : ℝ => ∫ y in Set.Ioc
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y)
      = fun θ : ℝ =>
          (∫ y in (0:ℝ)..(θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y)
          - (∫ y in (0:ℝ)..(θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k)), g y) := by
    funext θ
    exact intervalIntegral_Ioc_eq_primitive_sub hg (le_add_of_nonneg_right hc.le)
  rw [h_eq]
  apply Measurable.aemeasurable
  have hL2 : Measurable (fun θ : ℝ =>
      θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)) := hL.add measurable_const
  exact (hQcont.measurable.comp hL2).sub (hQcont.measurable.comp hL)

end Commons.Analysis.Fourier