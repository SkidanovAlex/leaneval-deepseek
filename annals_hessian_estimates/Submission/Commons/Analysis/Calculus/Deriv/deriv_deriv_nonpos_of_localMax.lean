import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus.Deriv

/-- If `f` is twice continuously differentiable at `x` and `x` is a local maximum of `f`,
then the second derivative of `f` at `x` is non-positive.

Indeed, if `deriv (deriv f) x > 0` then the second-derivative test
(`isLocalMin_of_deriv_deriv_pos`) together with Fermat's theorem (`deriv f x = 0`)
would exhibit `x` as a local *minimum* as well.  A point that is both a local minimum
and a local maximum is a point of local constancy, forcing `deriv f` to vanish on a
neighbourhood of `x` and hence `deriv (deriv f) x = 0`, a contradiction. -/
theorem deriv_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra hpos
  push Not at hpos
  -- `f` is continuous at `x`, and Fermat's theorem gives `deriv f x = 0`.
  have hcont : ContinuousAt f x := hf.continuousAt
  have hd : deriv f x = 0 := hmax.deriv_eq_zero
  -- If `f''(x) > 0` then `x` is also a local minimum.
  have hmin : IsLocalMin f x := isLocalMin_of_deriv_deriv_pos hpos hd hcont
  -- Hence `f` is locally constant around `x`.
  have hconst : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin, hmax] with y h1 h2
    exact le_antisymm h2 h1
  -- So `deriv f` vanishes on a neighbourhood of `x`.
  have hzero : deriv f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hconst
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with y hy
    have heq : f =ᶠ[𝓝 y] fun _ => f x :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy) hball
    rw [heq.deriv_eq]
    simp
  -- Consequently the second derivative at `x` is `0`, contradicting `hpos`.
  have hzero2 : deriv (deriv f) x = 0 := by
    rw [hzero.deriv_eq]
    simp
  linarith

end Commons.Analysis.Calculus.Deriv