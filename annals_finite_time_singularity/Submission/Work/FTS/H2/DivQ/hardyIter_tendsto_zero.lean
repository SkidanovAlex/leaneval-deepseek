import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.H2.DivQ

/-- Absolute continuity at the left endpoint of the integral: for `u` integrable on `(0,x₁)`,
the set integrals `∫_{x ∈ (0,δ)} u` tend to `0` as `δ → 0`.

Route: dominated convergence applied to `F δ = fun x => (Ioc 0 δ).indicator u x` with dominating
function `(Ioc 0 x₁).indicator (fun x => ‖u x‖)` (restrict to `δ < x₁`, which is an eventual
condition in `nhds 0`), using that for every `x` the indicator `1_{(0,δ)}(x)` vanishes for `δ`
small.  (For `δ ≤ 0` the set `Ioc 0 δ` is empty, so there is no issue on the left of `0`; `δ > x₁`
is avoided since `nhds 0` forces eventually `δ < x₁`.) -/
theorem hardyIter_tendsto_zero {u : ℝ → ℝ} {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hu : MeasureTheory.IntegrableOn u (Set.Ioc 0 x₁)) :
    Filter.Tendsto (fun δ : ℝ => ∫ x in Set.Ioc 0 δ, u x) (nhds (0 : ℝ)) (nhds 0) := by
  -- The dominating function: `u` restricted to `(0, x₁)`, in absolute value.
  have hbound : MeasureTheory.Integrable ((Set.Ioc 0 x₁).indicator (fun x => ‖u x‖))
      MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).mpr hu.norm
  -- Measurability of the approximants `(0,δ).indicator u`, for `δ < x₁`.
  have hmeas : ∀ᶠ δ : ℝ in nhds (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => (Set.Ioc 0 δ).indicator u x) MeasureTheory.volume := by
    filter_upwards [Iio_mem_nhds hx₁] with δ hδ
    exact (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      (hu.mono_set (Set.Ioc_subset_Ioc le_rfl hδ.le)).aestronglyMeasurable
  -- Domination, for `δ < x₁`.
  have hbd : ∀ᶠ δ : ℝ in nhds (0 : ℝ), ∀ᵐ x ∂MeasureTheory.volume,
      ‖(Set.Ioc 0 δ).indicator u x‖ ≤ (Set.Ioc 0 x₁).indicator (fun x => ‖u x‖) x := by
    filter_upwards [Iio_mem_nhds hx₁] with δ hδ
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    exact Set.indicator_le_indicator_of_subset (Set.Ioc_subset_Ioc le_rfl hδ.le)
      (fun x => norm_nonneg (u x)) x
  -- Pointwise convergence of the indicators to `0` (only `x > 0` is interesting, and then
  -- `x ∉ (0,δ)` as soon as `δ < x`).
  have hlim : ∀ᵐ x ∂MeasureTheory.volume,
      Filter.Tendsto (fun δ : ℝ => (Set.Ioc 0 δ).indicator u x) (nhds (0 : ℝ)) (nhds 0) := by
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : 0 < x
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Iio_mem_nhds hx] with δ hδ
      exact (Set.indicator_of_notMem (s := Set.Ioc 0 δ) (a := x)
        (fun hmem : x ∈ Set.Ioc 0 δ => absurd hmem.2 (not_le_of_gt hδ)) u).symm
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with δ
      exact (Set.indicator_of_notMem (s := Set.Ioc 0 δ) (a := x)
        (fun hmem : x ∈ Set.Ioc 0 δ => hx hmem.1) u).symm
  -- Dominated convergence for the filter `nhds 0`.
  have key : Filter.Tendsto (fun δ : ℝ => ∫ x, (Set.Ioc 0 δ).indicator u x) (nhds (0 : ℝ))
      (nhds (∫ x, (0 : ℝ) ∂MeasureTheory.volume)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (l := nhds (0 : ℝ))
      ((Set.Ioc 0 x₁).indicator (fun x => ‖u x‖)) hmeas hbd hbound hlim
  have key2 : Filter.Tendsto (fun δ : ℝ => ∫ x, (Set.Ioc 0 δ).indicator u x) (nhds (0 : ℝ))
      (nhds 0) := by
    simpa using key
  -- Identify the indicator integral with the set integral over `(0,δ)`.
  have heq : (fun δ : ℝ => ∫ x, (Set.Ioc 0 δ).indicator u x)
      = fun δ : ℝ => ∫ x in Set.Ioc 0 δ, u x :=
    funext fun δ => MeasureTheory.integral_indicator measurableSet_Ioc
  rw [heq] at key2
  exact key2

end Work.FTS.H2.DivQ
