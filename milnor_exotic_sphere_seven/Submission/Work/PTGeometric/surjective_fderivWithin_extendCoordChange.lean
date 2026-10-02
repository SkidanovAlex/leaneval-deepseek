import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Surjectivity of the derivative of a chart transition, on the model corner

For two charts `e`, `e'` of the maximal `C^n` atlas of a manifold with corners `M` (`n ≠ 0`)
around a point `x`, the model-space chart transition `I.extendCoordChange e e'` is a local
diffeomorphism of the model space, hence its derivative (taken within `range I`, which is what
one has available at a boundary point) at `e.extend I x` is surjective.

This is the statement used to transfer surjectivity of `mfderiv` between charts.

Mathlib proves the invertibility of the same derivative taken *within the source of the transition*
(`ModelWithCorners.isInvertible_fderivWithin_extendCoordChange`, used by
`ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas`).  Here the within-set is
the closed model corner `range I`.  The two derivatives agree because the source of the transition
is a neighbourhood of `e.extend I x` *within* `range I`
(`ModelWithCorners.extendCoordChange_source_mem_nhdsWithin'`) and is contained in `range I`
(`ModelWithCorners.extendCoordChange_source`).
-/

namespace Work.PTGeometric

lemma surjective_fderivWithin_extendCoordChange
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    {x : M} (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    Function.Surjective
      (fderivWithin ℝ (⇑(ModelWithCorners.extendCoordChange (I := I) e e')) (Set.range ⇑I)
        (⇑(e.extend I) x)) := by
  -- `e.extend I x` lies in the source of the chart transition.
  have hy : (e.extend I) x ∈ (I.extendCoordChange e e').source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    exact ⟨x, ⟨hxe, hxe'⟩, rfl⟩
  -- The source of the transition is contained in `range I` ...
  have hsub : (I.extendCoordChange e e').source ⊆ Set.range ⇑I := by
    rw [ModelWithCorners.extendCoordChange_source]
    exact Set.image_subset_range _ _
  -- ... and is a neighbourhood of `e.extend I x` within `range I`, so the two derivatives agree.
  have hdiff : DifferentiableWithinAt ℝ ⇑(I.extendCoordChange e e') (Set.range ⇑I)
      ((e.extend I) x) :=
    (ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := I) he he' hxe hxe').differentiableWithinAt
      hn
  have hEq : fderivWithin ℝ ⇑(I.extendCoordChange e e') (Set.range ⇑I) ((e.extend I) x)
      = fderivWithin ℝ ⇑(I.extendCoordChange e e') (I.extendCoordChange e e').source
          ((e.extend I) x) :=
    (fderivWithin_subset hsub (I.uniqueDiffOn_extendCoordChange_source _ hy) hdiff).symm
  rw [hEq]
  -- The derivative within the source is invertible, hence surjective.
  exact (ModelWithCorners.isInvertible_fderivWithin_extendCoordChange (I := I) hn he he' hy).surjective

end Work.PTGeometric
