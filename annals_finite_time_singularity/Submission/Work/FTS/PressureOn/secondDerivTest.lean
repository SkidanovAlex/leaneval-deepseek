import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

open scoped Topology

theorem secondDerivTest {f : ℝ → ℝ} {x₀ : ℝ} (hmax : IsLocalMax f x₀)
    (h2 : ContDiffAt ℝ 2 f x₀) : deriv (deriv f) x₀ ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x₀ := not_le.mp h
  -- Fermat's theorem: the first derivative vanishes at a local maximum.
  have hd : deriv f x₀ = 0 := hmax.deriv_eq_zero
  -- `h2` is only used here, to supply continuity at `x₀`.
  have hc : ContinuousAt f x₀ := h2.continuousAt
  -- The second-derivative test upgrades the positive second derivative to a local minimum.
  have hmin : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos hpos hd hc
  -- Being both a local min and a local max, `f` is eventually constant near `x₀`.
  have hconst : f =ᶠ[𝓝 x₀] fun _ => f x₀ := by
    filter_upwards [hmax, hmin] with x hx1 hx2 using le_antisymm hx1 hx2
  -- Hence `deriv f` is eventually `0` near `x₀`, and so is its derivative.
  have hzero : deriv (deriv f) x₀ = 0 := by
    have h1 : deriv (deriv f) =ᶠ[𝓝 x₀] deriv (deriv (fun _ : ℝ => f x₀)) := hconst.deriv.deriv
    have := h1.eq_of_nhds
    simpa using this
  linarith

end Work.FTS.PressureOn
