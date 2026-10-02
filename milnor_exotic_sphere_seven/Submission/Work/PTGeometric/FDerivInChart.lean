import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reading `mfderiv` in the preferred chart of the source

Two chart bookkeeping lemmas, used by
`Work.PTGeometric.submersionAt_boundary_fibre_of_mfderiv`.

* `Work.PTGeometric.hasFDerivWithinAt_comp_extChartAt_symm`: for a map `f : M → E'` differentiable
  at `x`, the function `z ↦ f ((extChartAt I x).symm z)` on the model space has, within `range I`,
  the ordinary derivative `mfderiv I 𝓘(𝕜,E') f x`.  (The outer chart of the definition of
  `writtenInExtChartAt` disappears because on the model space it is the identity,
  `extChartAt_self_eq`.)

* `Work.PTGeometric.hasFDerivWithinAt_extendCoordChange`: the chart transition
  `I.extendCoordChange e e'` is differentiable within `range I` at `e.extend I x`, with derivative
  its `fderivWithin`.

Both are chart-independent statements about Mathlib's calculus on manifolds with corners, and are
the bridge that lets us compute `mfderiv` of a function written in an arbitrary chart of the
maximal atlas even at *boundary* points (where `IsInteriorPoint` fails and the existing
`Work.ThomBordism.Transversality.TransversalApproximation.chartBridge` lemmas do not apply).
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false

/-- **`mfderiv` read in the preferred chart of the source.**  For `f : M → E'` differentiable at
`x`, the model-space function `z ↦ f ((extChartAt I x).symm z)` has ordinary derivative
`mfderiv I 𝓘(𝕜,E') f x` within `range I` at `(extChartAt I x) x`.  (This is
`writtenInExtChartAt` with the outer chart removed: on the model space `extChartAt` of the identity
structure is the identity.) -/
theorem hasFDerivWithinAt_comp_extChartAt_symm {f : M → E'} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, E') f x) :
    HasFDerivWithinAt (fun z : E => f ((extChartAt I x).symm z))
      (mfderiv I 𝓘(𝕜, E') f x) (Set.range I) ((extChartAt I x) x) := by
  have hwritten : writtenInExtChartAt I 𝓘(𝕜, E') x f =
      fun z : E => f ((extChartAt I x).symm z) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have h := hf.hasMFDerivAt
  unfold HasMFDerivAt at h
  rw [hwritten] at h
  exact h.2

/-- The zeroth coordinate functional of the model space `ℝⁿ`. -/
abbrev coordFun (n : ℕ) [NeZero n] : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin n => ℝ) 0

lemma coordFun_apply {n : ℕ} [NeZero n] (v : EuclideanSpace ℝ (Fin n)) :
    coordFun n v = v.ofLp 0 := by simp [coordFun]

/-- The extended chart `e.extend I` is differentiable at any point of `e.source`. -/
theorem mdifferentiableAt_extend {n : ℕ∞ω} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) {x : M} (hx : x ∈ e.source) (hn : n ≠ 0) :
    MDifferentiableAt I 𝓘(𝕜, E) (⇑(e.extend I)) x :=
  (e.contMDiffAt_extend he hx).mdifferentiableAt hn

/-- The chart transition is differentiable within `range I` at `e.extend I x`, with derivative
`fderivWithin` (computed within `range I`). -/
theorem hasFDerivWithinAt_extendCoordChange {n : ℕ∞ω} {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hn : n ≠ 0) :
    HasFDerivWithinAt (⇑(I.extendCoordChange e e'))
      (fderivWithin 𝕜 (⇑(I.extendCoordChange e e')) (Set.range I) (e.extend I x))
      (Set.range I) (e.extend I x) := by
  have hlt : e x ∈ (e.symm ≫ₕ e').source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨e.map_source hx, ?_⟩
    show e.symm (e x) ∈ e'.source
    rwa [OpenPartialHomeomorph.left_inv _ hx]
  have hmem : e.extend I x ∈ (I.extendCoordChange e e').source := by
    rw [ModelWithCorners.extendCoordChange_source]
    exact mem_image_of_mem _ hlt
  have hcont : ContDiffOn 𝕜 n (⇑(I.extendCoordChange e e')) (I.extendCoordChange e e').source :=
    I.contDiffOn_extendCoordChange he he'
  have hdiff : DifferentiableWithinAt 𝕜 (⇑(I.extendCoordChange e e'))
      (I.extendCoordChange e e').source (e.extend I x) :=
    (hcont.differentiableOn hn) _ hmem
  have hnhds : (I.extendCoordChange e e').source ∈ 𝓝[Set.range I] (e.extend I x) :=
    I.extendCoordChange_source_mem_nhdsWithin' hx hx'
  have h1 : HasFDerivWithinAt (⇑(I.extendCoordChange e e'))
      (fderivWithin 𝕜 (⇑(I.extendCoordChange e e')) (I.extendCoordChange e e').source
        (e.extend I x)) (I.extendCoordChange e e').source (e.extend I x) :=
    hdiff.hasFDerivWithinAt
  have h2 := h1.mono_of_mem_nhdsWithin hnhds
  have htarget : e.extend I x ∈ (e.extend I).target :=
    PartialEquiv.map_source _ (by simpa using hx)
  have huniq : UniqueDiffWithinAt 𝕜 (Set.range I) (e.extend I x) :=
    I.uniqueDiffOn _ (OpenPartialHomeomorph.extend_target_subset_range e htarget)
  rw [h2.fderivWithin huniq]
  exact h2

end

end Work.PTGeometric
