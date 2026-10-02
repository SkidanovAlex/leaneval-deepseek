import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

/-- Fibres of a local homeomorphism are discrete: near each point `x` of the fibre there is an
open set on which `f` is injective, so that set meets the fibre only in `x`. -/
theorem isDiscrete_preimage_singleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (y : Y) : IsDiscrete (f ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hf.isLocallyInjective x
  refine ⟨U, hUopen, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzU, hzf⟩
    exact hUinj hzU hxU (hzf.trans hx.symm)
  · rintro rfl
    exact ⟨hxU, hx⟩

end Work.SeedDyn
