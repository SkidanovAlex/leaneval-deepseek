import Mathlib

namespace Work.PertCrux

/-- The second iterate of the `dslope`-difference operator at the origin extracts the second
Taylor coefficient: for `f` analytic at `0`,

`((Function.swap dslope 0)^[2] f) 0 = iteratedDeriv 2 f 0 / 2`.

Indeed `(Function.swap dslope 0)^[2] f = dslope (dslope f 0) 0`, and evaluating at `0` gives
`deriv (dslope f 0) 0 = deriv (slope f 0) 0`, which is the coefficient of `z` in
`(f z - f 0)/z = f'(0) + (f''(0)/2) z + O z²`.

Formally: `AnalyticAt.hasFPowerSeriesAt` presents `f` as the power series
`∑ iteratedDeriv n f 0 / n! • zⁿ`, and
`HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope` (Mathlib,
`Analysis/Analytic/IsolatedZeros`) presents `(swap dslope 0)^[2] f` as the power series obtained by
applying `fslope` twice, whose `0`-th coefficient is the `2`-nd coefficient of `f`'s series, i.e.
`iteratedDeriv 2 f 0 / 2`. -/
lemma iterate_dslope_two_apply_zero {f : ℂ → ℂ} (han : AnalyticAt ℂ f 0) :
    ((Function.swap dslope (0 : ℂ))^[2] f) 0 = iteratedDeriv 2 f 0 / 2 := by
  have hp : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ fun n => iteratedDeriv n f 0 / n.factorial) 0 :=
    han.hasFPowerSeriesAt
  have h2 := HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope 2 hp
  have hcoeff : (FormalMultilinearSeries.fslope^[2] (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n f 0 / n.factorial))).coeff 0 = iteratedDeriv 2 f 0 / 2 := by
    rw [FormalMultilinearSeries.coeff_iterate_fslope]
    simp only [zero_add, FormalMultilinearSeries.coeff_ofScalars]
    norm_num
  rw [← h2.coeff_zero 1]
  exact hcoeff

end Work.PertCrux
