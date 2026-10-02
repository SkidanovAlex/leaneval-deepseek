import Mathlib
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold Topology
open Set Filter

namespace Work.PTGeometric

/-- The transition function between two extended charts of a `C^1` manifold with boundary,
`w ↦ (extChartAt I x) ((extChartAt I z).symm w)`, is differentiable (and hence `HasFDerivAt` its
own Fréchet derivative) at the image of any point of the source of the `z`-chart whose first
coordinate is positive, i.e. which lies in the interior of the model half-space.

The point of the hypothesis `hpos` is that at an interior point the half-space model
`range (𝓡∂ (n+1))` is a neighbourhood of the point, so the `within`-differentiability of
`(extChartAt I z).symm` supplied by the manifold structure upgrades to honest differentiability. -/
theorem transition_hasFDerivAt (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (z x : W) (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source)
    (hpos : 0 < (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z x) 0) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x)
          ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w))
      (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) x)
          ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm w))
        ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x))
      ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) x) := by
  apply DifferentiableAt.hasFDerivAt
  let I := modelWithCornersEuclideanHalfSpace (n + 1)
  change DifferentiableAt ℝ (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
      (extChartAt I x) ((extChartAt I z).symm w)) ((extChartAt I z) x)
  have hx' : x ∈ (extChartAt I z).source := by rw [extChartAt_source]; exact hx
  have hy : (extChartAt I z) x ∈ (extChartAt I z).target := (extChartAt I z).map_source hx'
  have hsymm : (extChartAt I z).symm ((extChartAt I z) x) = x := (extChartAt I z).left_inv hx'
  have hyint : (extChartAt I z) x ∈
      interior (range (I : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hpos
  have hmem : (range (I : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1)))) ∈
      𝓝 ((extChartAt I z) x) :=
    mem_of_superset (isOpen_interior.mem_nhds hyint) interior_subset
  have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) I 1 (extChartAt I z).symm
      ((extChartAt I z) x) :=
    (contMDiffWithinAt_extChartAt_symm_range (I := I) z hy).contMDiffAt hmem
  have h2 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1 (extChartAt I x) x :=
    contMDiffAt_extChartAt' (mem_chart_source _ _)
  have h2' : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1 (extChartAt I x)
      ((extChartAt I z).symm ((extChartAt I z) x)) := by
    rw [hsymm]; exact h2
  have h3 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
      ((extChartAt I x) ∘ (extChartAt I z).symm) ((extChartAt I z) x) :=
    h2'.comp _ h1
  have h4 : ContDiffAt ℝ 1 ((extChartAt I x) ∘ (extChartAt I z).symm) ((extChartAt I z) x) :=
    contMDiffAt_iff_contDiffAt.mp h3
  have h5 : DifferentiableAt ℝ ((extChartAt I x) ∘ (extChartAt I z).symm) ((extChartAt I z) x) :=
    h4.differentiableAt (by norm_num)
  simpa only [Function.comp_def] using h5

end Work.PTGeometric
