import Mathlib

namespace Work.HornCov

/-- Fibers of a local homeomorphism `p` over points of its base `S` are discrete: if
`y ∈ S` then `p ⁻¹' {y}` carries the discrete topology.

Indeed, for `z` in the fiber the local homeomorphism gives an open partial homeomorph
`e` with `z ∈ e.source` and `p = e`; the open set `e.source` cut down to the fiber is
exactly `{z}` (injectivity of `e`). -/
theorem discreteTopology_fiber {X : Type*} [TopologicalSpace X]
    {p : X → ℂ} {S : Set ℂ} (hloc : IsLocalHomeomorphOn p (p ⁻¹' S))
    {y : ℂ} (hy : y ∈ S) : DiscreteTopology ↥(p ⁻¹' {y}) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  have hzS : (z : X) ∈ p ⁻¹' S := by
    have h := z.2
    rw [Set.mem_preimage, Set.mem_singleton_iff] at h
    rw [Set.mem_preimage, h]
    exact hy
  obtain ⟨e, hzmem, hpe⟩ := hloc (z : X) hzS
  have hz'y : p (z : X) = y := by
    have h := z.2; rwa [Set.mem_preimage, Set.mem_singleton_iff] at h
  have hEq : (Subtype.val : ↥(p ⁻¹' {y}) → X) ⁻¹' e.source = {z} := by
    ext z'
    constructor
    · intro hz'
      refine Subtype.ext ?_
      have hz''y : p (z' : X) = y := by
        have h := z'.2; rwa [Set.mem_preimage, Set.mem_singleton_iff] at h
      have h1 : e (z' : X) = e (z : X) := by
        rw [← congrFun hpe (z' : X), ← congrFun hpe (z : X), hz''y, hz'y]
      exact e.injOn hz' hzmem h1
    · rintro rfl
      exact hzmem
  have hopen : IsOpen ((Subtype.val : ↥(p ⁻¹' {y}) → X) ⁻¹' e.source) :=
    e.open_source.preimage continuous_subtype_val
  rwa [hEq] at hopen

end Work.HornCov
