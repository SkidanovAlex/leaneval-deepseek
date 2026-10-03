import Mathlib

/-!
# Local injectivity of a holomorphic function with nonvanishing derivative

If `g : ℂ → ℂ` is analytic at `c` and `deriv g c ≠ 0`, then `g` is injective on some
ball centred at `c`.

This is the holomorphic local-injectivity (open-mapping) statement: an analytic function
with nonvanishing differential is conformal at the point, so it is locally one-to-one.
The proof goes through the (strict) inverse function theorem: `AnalyticAt.hasStrictDerivAt`
supplies `HasStrictDerivAt g (deriv g c) c`, and `HasStrictDerivAt.eventually_left_inverse`
provides a local left inverse of `g` around `c` (namely `HasStrictDerivAt.localInverse`),
which immediately yields injectivity on a neighbourhood of `c`, hence on a ball.
-/

open scoped Topology
open Filter

namespace Work.Repel

/-- A complex-analytic function with nonvanishing derivative at a point is injective on a
sufficiently small ball around that point. -/
theorem locally_inj_of_deriv_ne_zero {g : ℂ → ℂ} {c : ℂ} (hd : AnalyticAt ℂ g c)
    (hdc : deriv g c ≠ 0) : ∃ r : ℝ, 0 < r ∧ Set.InjOn g (Metric.ball c r) := by
  have hsd : HasStrictDerivAt g (deriv g c) c := hd.hasStrictDerivAt
  -- The inverse function theorem gives a local left inverse of `g` around `c`.
  have hleft : ∀ᶠ x in 𝓝 c,
      HasStrictDerivAt.localInverse g (deriv g c) c hsd hdc (g x) = x :=
    hsd.eventually_left_inverse hdc
  -- Extract the ball on which this left inverse identity holds.
  rw [Metric.eventually_nhds_iff] at hleft
  obtain ⟨ε, hεpos, hε⟩ := hleft
  refine ⟨ε, hεpos, ?_⟩
  intro x hx y hy hxy
  have hx' : HasStrictDerivAt.localInverse g (deriv g c) c hsd hdc (g x) = x :=
    hε (Metric.mem_ball.mp hx)
  have hy' : HasStrictDerivAt.localInverse g (deriv g c) c hsd hdc (g y) = y :=
    hε (Metric.mem_ball.mp hy)
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

end Work.Repel
