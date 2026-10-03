import Mathlib
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

namespace Work.Parab.inversion

/-- A holomorphic function that is injective on an open set has nowhere vanishing derivative.

The statement is local in the point, so no connectedness of `U` is needed: around a point
`z ∈ U` we may shrink `U` to a ball.  `DifferentiableOn` on an open set gives analyticity at `z`,
and injectivity on `U` restricts to injectivity on the ball; the ball version of the result is
`Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn` (whose argument is the classical one:
`deriv f z = 0` forces a zero of order `n ≥ 2` of `f - f z`, hence a local `n`-th power
`f - f z = (z ↦ z · r z) ^ n` with `r` nonvanishing, and a nontrivial `n`-th root of unity then
produces two distinct nearby points with the same `f`-value). -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) :
    ∀ z ∈ U, deriv f z ≠ 0 := by
  intro z hz
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr
    (hf.analyticAt (hU.mem_nhds hz)) (hinj.mono hrU)

end Work.Parab.inversion
