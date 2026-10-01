import Mathlib

namespace Work.LinnikAreas.Density4

open MeasureTheory

/-- `θ(t)/t` is uniformly bounded by `log 4` on all of `ℝ`: for `t < 2` (in particular `t < 1`)
`θ t = 0`, while for `t ≥ 1 > 0` Chebyshev's bound `θ t ≤ log 4 * t` applies. -/
lemma norm_theta_div_le (t : ℝ) : ‖Chebyshev.theta t / t‖ ≤ Real.log 4 := by
  rcases le_total (1:ℝ) t with h | h
  · have ht : 0 < t := lt_of_lt_of_le one_pos h
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Chebyshev.theta_nonneg t) ht.le),
      div_le_iff₀ ht]
    exact Chebyshev.theta_le_log4_mul_x (by linarith)
  · rw [Chebyshev.theta_eq_zero_of_lt_two (by linarith), zero_div, norm_zero]
    exact Real.log_nonneg (by norm_num)

/-- `θ(t)/t` is interval integrable on `[y,x]` when `y ≥ 1`: θ is a step function with
finitely many jumps and `1/t` is continuous on `[y,x] ∋ y > 0`.  Imports: Mathlib only
(`Mathlib.NumberTheory.Chebyshev` for `Chebyshev.theta`, `Chebyshev.theta_eq_sum_Icc`,
`Chebyshev.theta_eq_theta_coe_floor`).
Suggested route: on `[y,x]`,
`Chebyshev.theta t = Σ_{p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime} (Set.Ici (p:ℝ)).indicator
(fun _ => Real.log p) t`; each term is the indicator of a measurable set times a bounded
measurable function, hence integrable on the finite-measure set, and a finite sum of
integrable functions is integrable (`Integrable.indicator`, `IntegrableOn.of_bound`,
`Measure.integrableOn_of_bounded`, `IntervalIntegrable.congr`/`intervalIntegrable_congr`).
NOTE (reviewers): `IntervalIntegrable f volume a b` unfolds to
`IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume`, so both half-open
intervals must be handled; the `t ≤ 1` region is harmless because `Chebyshev.theta t = 0`
there (`Chebyshev.theta_eq_zero_of_lt_two`), so the apparent singularity of `1/t` at `t = 0`
never bites (the second component `Ioc x y` may contain such `t` when `x < y`). -/
theorem interval_integrable_theta_div (y x : ℝ) (hy : 1 ≤ y) :
    IntervalIntegrable (fun t => Chebyshev.theta t / t) volume y x := by
  have _hy : (1 : ℝ) ≤ y := hy
  -- θ is monotone, hence Borel measurable; division by `t` is measurable.
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Chebyshev.theta t / t) volume :=
    (Chebyshev.theta_mono.measurable.div measurable_id).aestronglyMeasurable
  -- `θ t / t` is uniformly bounded by `log 4`, and both `Ioc`s are finite-measure sets.
  unfold IntervalIntegrable
  refine ⟨Measure.integrableOn_of_bounded (M := Real.log 4) measure_Ioc_lt_top.ne hmeas ?_,
    Measure.integrableOn_of_bounded (M := Real.log 4) measure_Ioc_lt_top.ne hmeas ?_⟩ <;>
    exact Filter.Eventually.of_forall norm_theta_div_le

end Work.LinnikAreas.Density4
