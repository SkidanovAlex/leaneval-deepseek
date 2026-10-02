import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

/-!
# Continuity of the circle integral in a continuous parameter

`Work.PARIMPL.ParSplit.continuous_circleIntegral`:

if `f : ℂ → ℂ → ℂ` is continuous at every point of `U ×ˢ sphere w r` (as a function of the pair),
then for fixed `r > 0` the circle integral `t ↦ ∮ z in C(w, r), f t z` is continuous on `U`.

The proof rewrites the circle integral as the interval integral
`∫ θ in 0..2π, deriv (circleMap w r) θ • f t (circleMap w r θ)`, observes that the uncurried
integrand is jointly continuous on `↥U × ℝ` (the circle map lands in `sphere w r`, where `f` is
continuous), and applies `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.
-/

open scoped Interval Real
open Metric MeasureTheory

namespace Work.PARIMPL.ParSplit

theorem continuous_circleIntegral {f : ℂ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ∀ p ∈ U ×ˢ Metric.sphere w r, ContinuousAt (Function.uncurry f) p) :
    ContinuousOn (fun t => ∮ z in C(w, r), f t z) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : ↥U => ∮ z in C(w, r), f x.1 z)
  have hS : ContinuousOn (Function.uncurry f) (U ×ˢ Metric.sphere w r) :=
    fun p hp => (hcont p hp).continuousWithinAt
  have hΦc : Continuous (fun p : ↥U × ℝ => (p.1.1, circleMap w r p.2)) := by fun_prop
  have hΦm : ∀ p : ↥U × ℝ, (p.1.1, circleMap w r p.2) ∈ U ×ˢ Metric.sphere w r :=
    fun p => ⟨p.1.2, circleMap_mem_sphere w hr.le p.2⟩
  have h1 : Continuous (fun p : ↥U × ℝ => f p.1.1 (circleMap w r p.2)) :=
    hS.comp_continuous hΦc hΦm
  have h2 : Continuous (fun p : ↥U × ℝ => deriv (circleMap w r) p.2) := by
    simp only [deriv_circleMap]
    fun_prop
  have h3 : Continuous (fun p : ↥U × ℝ =>
      deriv (circleMap w r) p.2 • f p.1.1 (circleMap w r p.2)) :=
    h2.smul h1
  have hmain : Continuous
      (fun x : ↥U => ∫ θ in (0 : ℝ)..2 * π,
        deriv (circleMap w r) θ • f x.1 (circleMap w r θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume)
      (f := fun (x : ↥U) (θ : ℝ) => deriv (circleMap w r) θ • f x.1 (circleMap w r θ))
      h3 0 (2 * π)
  simpa only [circleIntegral] using hmain

end Work.PARIMPL.ParSplit
