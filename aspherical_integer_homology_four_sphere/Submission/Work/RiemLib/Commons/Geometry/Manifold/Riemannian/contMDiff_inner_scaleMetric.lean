import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Riemannian

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.Riemannian

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Metric

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, IsTopologicalAddGroup (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Smoothness survives scaling of the fibre metric by a constant.**  If the section
`b ↦ ⟨b, g.inner b⟩` of the trivial bundle with fibre `F →L[ℝ] F →L[ℝ] ℝ` is `C^∞`, and
`g'.inner b = c * g.inner b`, then `b ↦ ⟨b, g'.inner b⟩` is `C^∞` too.  This is the
`IsContMDiffRiemannianBundle`-preservation part of the metric-scaling API. -/
theorem contMDiff_inner_scaleMetric
    (g g' : RiemannianMetric E) {c : ℝ}
    (hinner : ∀ (b : B) (v w : E b), g'.inner b v w = c * g.inner b v w)
    (hg : ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (F →L[ℝ] F →L[ℝ] ℝ))) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun b : B => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g.inner b))) :
    ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (F →L[ℝ] F →L[ℝ] ℝ))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun b : B => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g'.inner b)) := by
  -- The scaled metric is the pointwise scalar multiple of `g` in the hom-bundle
  -- `fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ`.
  have hinner' : ∀ b : B, g'.inner b = c • g.inner b := by
    intro b
    ext v w
    simp [hinner b v w]
  -- `ContMDiff.const_smul_section` gives smoothness of the constant multiple of a smooth
  -- section, and the two sections agree pointwise.
  intro b₀
  refine ((hg.const_smul_section (a := c)) b₀).congr_of_eventuallyEq ?_
  filter_upwards with b
  simp only [TotalSpace.mk_inj]
  exact hinner' b

end Commons.Geometry.Manifold.Riemannian