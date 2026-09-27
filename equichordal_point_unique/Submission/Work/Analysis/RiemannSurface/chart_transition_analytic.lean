import Mathlib

/-!
# Chart transitions of a complex one-manifold are holomorphic

For `X` a complex one-dimensional manifold (`ChartedSpace ℂ X` together with
`IsManifold (modelWithCornersSelf ℂ ℂ) 1 X`), the transition between two charts is holomorphic.
This is the single new input needed by rung (B2) of `NOTES_divisor_chapter_plan.md` §14 — the
chart-local `∂̄`-solvability for `(0,1)`-forms — because
`Work.Analysis.Complex.DbarCauchy.dbar_comp_analyticAt` (the `conj(φ')` change-of-variables rule)
then converts a solution built in one chart into a solution in every chart.

The proof is the groupoid chain
`IsManifold.subset_maximalAtlas` → `StructureGroupoid.compatible_of_mem_maximalAtlas`
→ `mem_groupoid_of_pregroupoid` → `contMDiffOn_iff_contDiffOn` → `ContDiffOn.differentiableOn`
→ `DifferentiableOn.analyticAt`.
-/

open scoped Manifold Topology

noncomputable section

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart transitions of a complex one-manifold are holomorphic.**  For two atlas charts `c₀`,
`c₁` of `X`, the transition `c₁.symm ≫ₕ c₀` (read `c₁`-coordinates into `c₀`-coordinates) is
complex-analytic at every point of its source. -/
theorem analyticAt_transition {c₀ c₁ : OpenPartialHomeomorph X ℂ} (hc₀ : c₀ ∈ atlas ℂ X)
    (hc₁ : c₁ ∈ atlas ℂ X) {w : ℂ} (hw : w ∈ (c₁.symm ≫ₕ c₀).source) :
    AnalyticAt ℂ ((c₁.symm ≫ₕ c₀ : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ) w := by
  have hm₀ : c₀ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X :=
    IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ ℂ) (n := 1) (M := X) hc₀
  have hm₁ : c₁ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X :=
    IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ ℂ) (n := 1) (M := X) hc₁
  have hmem : (c₁.symm ≫ₕ c₀) ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas
      (G := contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)) hm₁ hm₀
  have hcd : ContDiffOn ℂ 1 ((c₁.symm ≫ₕ c₀ : OpenPartialHomeomorph ℂ ℂ) : ℂ → ℂ)
      (c₁.symm ≫ₕ c₀).source := by
    have h := (mem_groupoid_of_pregroupoid.mp hmem).1
    simpa [contDiffPregroupoid] using h
  exact (hcd.differentiableOn one_ne_zero).analyticAt
    ((c₁.symm ≫ₕ c₀).open_source.mem_nhds hw)

end Work.Analysis.RiemannSurface
