import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.MetricSpace.Basic

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

/-- If `f` has a local maximum at `t`, has derivative `0` at `t`, and its derivative `deriv f`
is differentiable at `t` with derivative `c`, then `c ≤ 0`.

Indeed, if `c > 0` the second-derivative test (`isLocalMin_of_deriv_deriv_pos`) together with
`deriv f t = 0` would make `t` a local *minimum* of `f` as well. A point that is both a local
minimum and a local maximum is a point of local constancy, forcing `deriv f` to vanish on a
neighbourhood of `t` and hence `deriv (deriv f) t = 0`, contradicting `c > 0`. -/
theorem deriv_deriv_nonpos_of_localMax {f : ℝ → ℝ} {t c : ℝ}
    (hf : HasDerivAt f 0 t) (h : HasDerivAt (deriv f) c t)
    (hmax : ∀ᶠ s in nhds t, f s ≤ f t) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  -- `hmax` is a local maximum.
  have hmaxI : IsLocalMax f t := hmax
  -- If `c > 0` then `t` is also a local minimum of `f`.
  have hmin : IsLocalMin f t :=
    isLocalMin_of_deriv_deriv_pos (by rw [h.deriv]; exact hc) hf.deriv hf.continuousAt
  -- Hence `f` is locally constant around `t`.
  have hconst : f =ᶠ[𝓝 t] fun _ => f t := by
    filter_upwards [hmin, hmaxI] with y h1 h2
    exact le_antisymm h2 h1
  -- So `deriv f` vanishes on a neighbourhood of `t`.
  have hzero : deriv f =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hconst
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with y hy
    have heq : f =ᶠ[𝓝 y] fun _ => f t :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy) hball
    rw [heq.deriv_eq]
    simp
  -- Consequently the second derivative at `t` is `0`, contradicting `c > 0`.
  have hzero2 : deriv (deriv f) t = 0 := by
    rw [hzero.deriv_eq]
    simp
  rw [h.deriv] at hzero2
  linarith

end Commons.Analysis.Calculus
