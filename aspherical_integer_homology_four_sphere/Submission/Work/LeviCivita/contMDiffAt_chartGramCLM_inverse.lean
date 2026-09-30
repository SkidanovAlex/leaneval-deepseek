import Mathlib
import Submission.Work.LeviCivita.ChartMetric
import Submission.Work.LeviCivita.contDiffAt_chartGramCLM
import Submission.Work.LeviCivita.contDiffAt_inverse_of_posDef
import Submission.Work.LeviCivita.isInvertible_of_posDef

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LeviCivita

open scoped Manifold ContDiff Bundle Topology in
theorem contMDiffAt_chartGramCLM_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) :
    ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) ∞
      (fun x : M ↦ (Work.LeviCivita.chartGramCLM (I := I) x₀ x).inverse) p := by
  -- Read the statement in the chart at `x₀`: smoothness of `f : M → F` at `p` is smoothness of
  -- `f ∘ (extChartAt I x₀).symm` on `range I` at `extChartAt I x₀ p`; `I` is boundaryless, so
  -- `range I = univ` and a `ContDiffWithinAt` on `univ` is a `ContDiffAt`.
  rw [contMDiffAt_iff_source_of_mem_source (I := I) (x := x₀) (x' := p) hp]
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ]
  have hsrc : p ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
    (extChartAt I x₀).left_inv hsrc
  -- The chart metric is `C^∞` in the chart coordinates (`contDiffAt_chartGramCLM`).
  have hG : ContDiffAt ℝ ∞
      (fun q : E ↦ Work.LeviCivita.chartGramCLM (I := I) x₀ ((extChartAt I x₀).symm q))
      (extChartAt I x₀ p) :=
    Work.LeviCivita.contDiffAt_chartGramCLM (I := I) x₀ p hp
  -- It is positive definite at `p`, hence invertible there.
  have hI : (Work.LeviCivita.chartGramCLM (I := I) x₀
      ((extChartAt I x₀).symm (extChartAt I x₀ p))).IsInvertible := by
    rw [hleft]
    exact Work.LeviCivita.isInvertible_of_posDef _
      (fun v hv ↦ Work.LeviCivita.chartGram_posDef (I := I) x₀ p hp hv)
  -- `ContinuousLinearMap.inverse` is `C^∞` at an invertible point, so compose with `hG`.
  have h1 : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
      (Work.LeviCivita.chartGramCLM (I := I) x₀
        ((extChartAt I x₀).symm (extChartAt I x₀ p))) := hI.contDiffAt_map_inverse
  have h2 := h1.comp (extChartAt I x₀ p) hG
  exact h2

end Work.LeviCivita
