import Mathlib

namespace Work.RPB1a

/-- An analytic function with nonvanishing derivative at a point is injective on a neighbourhood
of that point (local injectivity, a weak form of the inverse function theorem). -/
theorem exists_nhds_injOn_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ f z) (h : deriv f z ≠ 0) :
    ∃ U ∈ nhds z, Set.InjOn f U := by
  -- `AnalyticAt` gives a strict derivative; the inverse function theorem then provides a local
  -- left inverse, which immediately forces injectivity.
  have hev := hz.hasStrictDerivAt.eventually_left_inverse h
  rw [Filter.eventually_iff_exists_mem] at hev
  obtain ⟨U, hU, hUm⟩ := hev
  refine ⟨U, hU, fun x hx y hy hxy => ?_⟩
  have hx' := hUm x hx
  have hy' := hUm y hy
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

end Work.RPB1a
