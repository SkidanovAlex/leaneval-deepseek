import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability and invertibility of a chart transition at an interior point

For two charts `e`, `e'` of the maximal `C^n` atlas of a manifold with corners `M` (`n ≠ 0`) and a
point `z` which lies both in the source of the model chart transition `I.extendCoordChange e e'`
and in the *interior* of the model corner `range I`, the transition is differentiable at `z` in
the ambient sense (not merely within `range I`), and its full Fréchet derivative `fderiv` there is
invertible.

Both facts are immediate from the corresponding "within the source" statements
(`ModelWithCorners.contDiffOn_extendCoordChange` and
`ModelWithCorners.isInvertible_fderivWithin_extendCoordChange`) once one observes that the source
of the transition is a full neighbourhood of `z`: it is a neighbourhood of `z` within `range I`
(`ModelWithCorners.extendCoordChange_source_mem_nhdsWithin`) and `range I` itself is a
neighbourhood of `z` precisely because `z` is an interior point of `range I`.
-/

namespace Work.ThomBordism.PosAtlas

open Set Filter
open scoped Topology

theorem differentiableAt_extendCoordChange_isInvertible
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
    (e e' : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hn : n ≠ 0) {z : E}
    (hz : z ∈ (I.extendCoordChange e e').source)
    (hzint : z ∈ interior (Set.range (I : H → E))) :
    DifferentiableAt 𝕜 (⇑(I.extendCoordChange e e')) z ∧
      (fderiv 𝕜 (⇑(I.extendCoordChange e e')) z).IsInvertible := by
  -- `z` is an interior point of the model corner, so `range I` is a genuine neighbourhood of `z`.
  have hrange : Set.range (I : H → E) ∈ 𝓝 z :=
    mem_interior_iff_mem_nhds.1 hzint
  -- The source of the transition is a neighbourhood of `z` within `range I`.
  have hsrc' : (I.extendCoordChange e e').source ∈ 𝓝[Set.range (I : H → E)] z :=
    I.extendCoordChange_source_mem_nhdsWithin hz
  -- Hence it is a genuine neighbourhood of `z`: it contains the intersection of a neighbourhood
  -- of `z` with `range I`, and `range I` is itself a neighbourhood of `z`.
  obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsrc'
  have hsrc : (I.extendCoordChange e e').source ∈ 𝓝 z :=
    mem_of_superset (inter_mem hu hrange) (fun y hy => hus ⟨hy.1, hy.2⟩)
  refine ⟨?_, ?_⟩
  · -- Differentiability: the transition is `C^n` on its source, and `n ≠ 0`.
    have hd : DifferentiableWithinAt 𝕜 (⇑(I.extendCoordChange e e'))
        (I.extendCoordChange e e').source z :=
      (I.contDiffOn_extendCoordChange he he').differentiableOn hn z hz
    exact hd.differentiableAt hsrc
  · -- Invertibility: the derivative within the source is invertible, and the two derivatives
    -- agree because the source is a neighbourhood of `z`.
    have h := I.isInvertible_fderivWithin_extendCoordChange hn he he' hz
    rwa [fderivWithin_of_mem_nhds hsrc] at h

end Work.ThomBordism.PosAtlas
