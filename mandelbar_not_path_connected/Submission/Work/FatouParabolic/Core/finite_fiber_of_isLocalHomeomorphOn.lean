import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-- If `f` is a local homeomorphism on the preimage of `s` and every fibre over a point of `s`
is compact, then every such fibre is finite.

This is the standard fact that a compact set carrying the discrete topology is finite: a local
homeomorphism is locally injective, so each fibre over a point of `s` is discrete in the induced
topology, and a compact discrete set is finite. -/
theorem finite_fiber_of_isLocalHomeomorphOn {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {s : Set X} (hloc : IsLocalHomeomorphOn f (f ⁻¹' s))
    (hcomp : ∀ x ∈ s, IsCompact (f ⁻¹' {x})) : ∀ x ∈ s, (f ⁻¹' {x}).Finite := by
  intro x hx
  refine (hcomp x hx).finite ?_
  -- `f⁻¹' {x}` is contained in `f⁻¹' s`, where `f` is a local homeomorphism.
  have hsub : f ⁻¹' {x} ⊆ f ⁻¹' s := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
    simp only [Set.mem_preimage]
    rw [hy]; exact hx
  -- Hence `f⁻¹' {x}` is discrete as soon as its image under `f` is discrete; but its image is
  -- contained in the singleton `{x}`.
  refine IsLocalHomeomorphOn.isDiscrete_of_image (hloc.mono hsub) ?_
  apply Set.Subsingleton.isDiscrete
  rintro a ⟨y, hy, rfl⟩ b ⟨z, hz, rfl⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy hz
  rw [hy, hz]

end Work.FatouParabolic.Core
