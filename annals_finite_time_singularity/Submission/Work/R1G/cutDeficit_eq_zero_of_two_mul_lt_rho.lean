import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.R1G.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set
open scoped Topology

namespace Work.R1G

/-- **The cut-off deficit vanishes in the far field.**  Off the radius `2L` the cut-off factor
`χ(ρ/L)` is identically `0` in a whole neighbourhood of `ρ/L` (indeed `χ ≡ 0` on `[2,∞)`), so its
derivative `χ'(ρ/L)/L = chiRad P r z` vanishes and the whole deficit
`cutDeficit P ψ W r z t = chiRad P r z * (…) * W r z t` collapses. -/
theorem cutDeficit_eq_zero_of_two_mul_lt_rho {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (ψ W : ℝ → ℝ → ℝ → ℝ) {r z t : ℝ} (h : 2 * P.L < Work.Cyl.rhoP r z) :
    Work.R1G.cutDeficit P ψ W r z t = 0 := by
  rw [Work.R1G.cutDeficit_apply, Work.R1G.chiRad]
  have hx2 : 2 < Work.Cyl.rhoP r z / P.L := by
    rw [lt_div_iff₀ P.hL]
    linarith
  have hderiv : deriv Work.Stability.chi (Work.Cyl.rhoP r z / P.L) = 0 := by
    have hev : ∀ᶠ y in 𝓝 (Work.Cyl.rhoP r z / P.L), Work.Stability.chi y = 0 := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨(Work.Cyl.rhoP r z / P.L - 2) / 2, by linarith, ?_⟩
      intro y hy
      rw [Real.dist_eq] at hy
      have hy2 : 2 < y := by
        have := abs_lt.mp hy
        linarith [this.1, this.2]
      exact Work.Stability.chi_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact deriv_const _ 0
  rw [hderiv]
  ring

end Work.R1G
