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

/-- **The coordinate derivative of a curve.**  If `γ : ℝ → M` is differentiable at `t` and
`γ t` lies in the source of the chart at `x₀`, then the manifold derivative of the coordinate
curve `extChartAt I x₀ ∘ γ : ℝ → E` is the coordinate expression (through the tangent-bundle
trivialisation at `x₀`) of `mfderiv 𝓘(ℝ) I γ t`. -/
theorem mfderiv_extChartAt_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x₀ : M} {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) (hx : γ t ∈ (chartAt H x₀).source) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ((extChartAt I x₀) ∘ γ) t =
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t)).comp
        (mfderiv 𝓘(ℝ) I γ t) := by
  -- Replace the trivialisation's linear map by the manifold derivative of the chart.
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hx]
  -- Chain rule for `mfderiv`.
  exact mfderiv_comp t (mdifferentiableAt_extChartAt hx) hγ

end Commons.Geometry.Manifold.Tangent