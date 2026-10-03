import Mathlib

namespace Work.L61.Branch

open Filter
open scoped Topology

/-- **Analyticity of a continuous lift.**

If `g` is analytic at `w` with non-vanishing derivative, `f` is analytic at `z₀`, and a
continuous `ψ` on a neighbourhood `U` of `z₀` satisfies `g (ψ z) = f z` for `z ∈ U` with
`ψ z₀ = w`, then `ψ` is analytic at `z₀`.

Indeed let `r` be the local inverse of `g` at `w` (which exists and is analytic near `g w`
because `deriv g w ≠ 0`).  On `U` we have `r (f z) = r (g (ψ z)) = ψ z`: the last equality holds
for `z` close to `z₀` because `ψ` is continuous at `z₀` with `ψ z₀ = w` and `r ∘ g = id` near
`w`.  Hence `ψ` agrees near `z₀` with the analytic function `r ∘ f`. -/
theorem analyticAt_of_lift {g f ψ : ℂ → ℂ} {U : Set ℂ} {z₀ w : ℂ}
    (hUo : IsOpen U) (hz₀U : z₀ ∈ U) (hg : AnalyticAt ℂ g w) (hg' : deriv g w ≠ 0)
    (hf : AnalyticAt ℂ f z₀) (hψcomp : ∀ z ∈ U, g (ψ z) = f z)
    (hψcont : ContinuousOn ψ U) (hψz₀ : ψ z₀ = w) : AnalyticAt ℂ ψ z₀ := by
  -- `r` is the local inverse of `g` at `w`.
  let r : ℂ → ℂ := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt ℂ r (g w) := hg.analyticAt_localInverse hg'
  have hgw : g w = f z₀ := by rw [← hψz₀, hψcomp z₀ hz₀U]
  have hra' : AnalyticAt ℂ r (f z₀) := hgw ▸ hra
  -- `r ∘ f` is analytic at `z₀`.
  have hcomp : AnalyticAt ℂ (r ∘ f) z₀ := hra'.comp hf
  -- and it agrees with `ψ` near `z₀`.
  refine hcomp.congr ?_
  have hcont : ContinuousAt ψ z₀ := hψcont.continuousAt (hUo.mem_nhds hz₀U)
  have hcontw : Tendsto ψ (𝓝 z₀) (𝓝 w) := by rw [← hψz₀]; exact hcont
  have hleft : ∀ᶠ z in 𝓝 z₀, r (g (ψ z)) = ψ z :=
    hcontw.eventually (hg.hasStrictDerivAt.eventually_left_inverse hg')
  filter_upwards [hUo.mem_nhds hz₀U, hleft] with z hzU hzr
  rw [Function.comp_apply, ← hψcomp z hzU]
  exact hzr

end Work.L61.Branch
