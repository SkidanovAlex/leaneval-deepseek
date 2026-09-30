import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.Tangent

open scoped _root_.Manifold _root_.ContDiff
open Filter

/-- **The velocity of a curve given in coordinates.**  If `u : ℝ → E` has derivative `v` at `t`,
stays in the target of the chart at `x₀` near `t`, and `u t` is in that target, then the curve
`s ↦ (extChartAt I x₀).symm (u s)` in `M` has velocity the coordinate vector `v`, transported to
`T M` by the inverse tangent-bundle trivialisation at `x₀`. -/
theorem hasMFDerivAt_extChartAt_symm_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x₀ : M} {u : ℝ → E} {t : ℝ} {v : E}
    (hu : HasDerivAt u v t) (ht : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in nhds t, u s ∈ (extChartAt I x₀).target) :
    HasMFDerivAt 𝓘(ℝ) I (fun s => (extChartAt I x₀).symm (u s)) t
      (((trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u t))) ∘L
        (ContinuousLinearMap.toSpanSingleton ℝ v)) := by
  have hsource : (extChartAt I x₀).symm (u t) ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target ht
  have hchart : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I) x₀] at hsource
  have htarget : extChartAt I x₀ ((extChartAt I x₀).symm (u t)) = u t :=
    (extChartAt I x₀).right_inv ht
  -- The curve `u` is manifold-differentiable with derivative `toSpanSingleton v`.
  have hu_mf : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) u t (ContinuousLinearMap.toSpanSingleton ℝ v) :=
    hu.hasFDerivAt.hasMFDerivAt
  -- The inverse chart is manifold-differentiable within `range I`.
  have hg : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I) (u t)
      (mfderiv[Set.range I] (extChartAt I x₀).symm (u t)) :=
    (mdifferentiableWithinAt_extChartAt_symm ht).hasMFDerivWithinAt
  -- Chain rule, restricted to the set where `u` takes values in the chart target.
  have hcomp : HasMFDerivWithinAt 𝓘(ℝ) I ((extChartAt I x₀).symm ∘ u)
      (u ⁻¹' (extChartAt I x₀).target) t
      ((mfderiv[Set.range I] (extChartAt I x₀).symm (u t)) ∘L
        (ContinuousLinearMap.toSpanSingleton ℝ v)) :=
    HasMFDerivWithinAt.comp t hg (hu_mf.hasMFDerivWithinAt.mono (Set.subset_univ _))
      (fun z hz => extChartAt_target_subset_range x₀ hz)
  -- The set is a neighbourhood of `t`, so the within-derivative is a genuine derivative.
  have hfull := hcomp.hasMFDerivAt hstay
  -- Identify the derivative with the inverse tangent-bundle trivialisation at `x₀`.
  have hsyml : (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm (u t))
      = mfderiv[Set.range I] (extChartAt I x₀).symm (u t) := by
    rw [TangentBundle.symmL_trivializationAt (I := I) hchart, htarget]
  rw [← hsyml] at hfull
  exact hfull

end Commons.Geometry.Manifold.Tangent