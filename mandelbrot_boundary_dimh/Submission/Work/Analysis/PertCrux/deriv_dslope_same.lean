import Mathlib

-- The stated hypothesis `hf' : DifferentiableAt ℂ (deriv f) c` is not needed by the proof below,
-- because `hf` (differentiability on an *open* set) already makes `f` analytic at `c`.
set_option linter.unusedVariables false

namespace Work.Analysis.PertCrux

/-- **Derivative of the divided slope at the base point, analytic form.**

If `f` is analytic at `c` then the difference quotient `dslope f c` (which equals
`(f z - f c)/(z - c)` for `z ≠ c` and `deriv f c` at `z = c`) has derivative `f''(c)/2` at `c`.

Indeed, `AnalyticAt.hasFPowerSeriesAt` presents `f` as the power series
`∑ₙ (iteratedDeriv n f c / n!) zⁿ` centred at `c`, and `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`
presents `dslope f c` as `fslope` of that series.  The derivative of a power series at its centre is
the coefficient of `z`, so `deriv (dslope f c) c = (p.fslope).coeff 1 = p.coeff 2
= iteratedDeriv 2 f c / 2 = deriv (deriv f) c / 2`. -/
theorem deriv_dslope_of_analyticAt {f : ℂ → ℂ} {c : ℂ} (han : AnalyticAt ℂ f c) :
    deriv (dslope f c) c = deriv (deriv f) c / 2 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n f c / n.factorial) with hpdef
  have hp : HasFPowerSeriesAt f p c := by
    rw [hpdef]; exact han.hasFPowerSeriesAt
  have hds : HasFPowerSeriesAt (dslope f c) p.fslope c := hp.has_fpower_series_dslope_fslope
  -- the derivative at the centre is the first coefficient of the power series
  have hder : deriv (dslope f c) c = p.fslope.coeff 1 := by
    rw [hds.deriv]
    rfl
  -- `fslope` shifts the coefficients down by one
  have hp2 : p.fslope.coeff 1 = p.coeff 2 := by
    rw [FormalMultilinearSeries.coeff_fslope]
  -- the coefficients of `ofScalars` are the Taylor coefficients
  have hcoeff : p.coeff 2 = iteratedDeriv 2 f c / 2 := by
    rw [hpdef, FormalMultilinearSeries.coeff_ofScalars]
    norm_num
  have hiter : iteratedDeriv 2 f c = deriv (deriv f) c := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hder, hp2, hcoeff, hiter]

/-- For `f` complex-differentiable on an open set `U ∋ c` whose derivative is again differentiable
at `c`, the divided slope `dslope f c` has derivative `f''(c)/2` at `c`. -/
theorem deriv_dslope_same {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} (hU : IsOpen U) (hc : c ∈ U)
    (hf : DifferentiableOn ℂ f U) (hf' : DifferentiableAt ℂ (deriv f) c) :
    deriv (dslope f c) c = deriv (deriv f) c / 2 :=
  deriv_dslope_of_analyticAt (hf.analyticAt (hU.mem_nhds hc))

end Work.Analysis.PertCrux
