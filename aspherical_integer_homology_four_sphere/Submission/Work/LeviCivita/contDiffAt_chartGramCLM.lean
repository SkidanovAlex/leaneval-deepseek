import Mathlib
import Submission.Work.LeviCivita.ChartMetric

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LeviCivita

open scoped Manifold ContDiff Bundle Topology
open Submission.Geodesic Submission.ChartConnection

/-- **Smoothness of the chart metric as a continuous bilinear form, in chart coordinates.**

For `p` in the source of the chart at `x₀`, the function
`q ↦ chartGramCLM x₀ ((extChartAt I x₀).symm q)`, from the model space `E` to the space of
continuous bilinear forms `E →L[ℝ] E →L[ℝ] ℝ`, is `C^∞` at `extChartAt I x₀ p`.

The proof reduces the statement to its scalar matrix entries via
`contDiffWithinAt_clm_apply` (valid because `E` is finite dimensional): for fixed `a b : E` the
function `q ↦ chartGram x₀ ((extChartAt I x₀).symm q) a b` is the metric applied to the frame
sections with coordinates `a` and `b`.  Those sections are smooth on the chart
(`contMDiffAt_frameSection`) and the scalar product of two smooth sections of a Riemannian bundle
is smooth (`ContMDiffAt.inner_bundle`), so the chart metric is `C^∞` in the base point; rewriting
with `contMDiffAt_iff_source_of_mem_source` and `[I.Boundaryless]` (so that `range I = univ`) turns
this into `C^∞`-ness in the chart coordinates. -/
theorem contDiffAt_chartGramCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) :
    ContDiffAt ℝ ∞ (fun q : E ↦
      Work.LeviCivita.chartGramCLM (I := I) x₀ ((extChartAt I x₀).symm q))
      (extChartAt I x₀ p) := by
  -- The chart metric is smooth in the base point on the chart: for fixed coordinates `a b`,
  -- `q ↦ chartGram x₀ q a b` is the scalar product of two smooth frame sections.
  have hscalar : ∀ a b : E, ContDiffAt ℝ ∞
      (fun q : E ↦ chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a b)
      (extChartAt I x₀ p) := by
    intro a b
    have hmd : ContMDiffAt I 𝓘(ℝ) ∞ (fun q : M ↦ chartGram (I := I) x₀ q a b) p :=
      ContMDiffAt.inner_bundle (contMDiffAt_frameSection (I := I) x₀ a hp)
        (contMDiffAt_frameSection (I := I) x₀ b hp)
    -- pass to the chart at `x₀`: smoothness of `f : M → ℝ` at `p` is smoothness of
    -- `f ∘ (extChartAt I x₀).symm` on `range I` at `extChartAt I x₀ p`
    rw [contMDiffAt_iff_source_of_mem_source (I := I) (x := x₀) (x' := p) hp] at hmd
    rw [contMDiffWithinAt_iff_contDiffWithinAt] at hmd
    -- `I` is boundaryless, so `range I = univ`
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at hmd
    exact hmd
  -- A map into a finite-dimensional space of continuous linear maps is `C^∞` as soon as all its
  -- applications are; apply this twice to reduce to the scalar entries.
  change ContDiffWithinAt ℝ ∞
    (fun q : E ↦ Work.LeviCivita.chartGramCLM (I := I) x₀ ((extChartAt I x₀).symm q))
    Set.univ (extChartAt I x₀ p)
  rw [contDiffWithinAt_clm_apply]
  intro a
  rw [contDiffWithinAt_clm_apply]
  intro b
  simpa only [contDiffWithinAt_univ, chartGramCLM_apply] using hscalar a b

end Work.LeviCivita
