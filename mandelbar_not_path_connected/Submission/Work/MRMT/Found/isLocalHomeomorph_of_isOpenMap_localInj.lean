import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- A continuous open map `f : ℂ → ℂ` that is injective on a neighbourhood of each point is a local
homeomorphism.

Proof sketch: use `isLocalHomeomorph_iff_isOpenEmbedding_restrict`.  For `z`, take an open
`U ∋ z` contained in an injectivity neighbourhood (`hli z` shrunk to an open set).  Then
`U.domRestrict f : U → ℂ` is continuous, injective, and an open map (a set relatively open in `U`
is open in `ℂ`, since `U` is open, so its image under the open map `f` is open); hence
`Topology.IsOpenEmbedding (U.domRestrict f)` by
`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`. -/
theorem isLocalHomeomorph_of_isOpenMap_localInj {f : ℂ → ℂ} (hcont : Continuous f)
    (hopen : IsOpenMap f) (hli : ∀ z : ℂ, ∃ U : Set ℂ, U ∈ nhds z ∧ Set.InjOn f U) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro z
  obtain ⟨U, hU, hInj⟩ := hli z
  -- shrink the injectivity neighbourhood to an open one
  refine ⟨interior U, isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU), ?_⟩
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuousOn_iff_continuous_domRestrict.mp (hcont.continuousOn.mono interior_subset)
  · exact Set.injOn_iff_injective.mp (hInj.mono interior_subset)
  · exact hopen.domRestrict isOpen_interior

end Work.MRMT.Found
