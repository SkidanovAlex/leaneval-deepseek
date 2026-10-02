import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

/-- If `p : E → X` is a covering map over a path-connected base `X`, and the fiber of `p` over
`p e₀` is a singleton, then `p` is bijective.

Surjectivity follows from path lifting (`IsCoveringMap.comp_subtypeVal_pathComponent_surjective`):
every point of `X` is joined to `p e₀` by a path, whose lift starting at `e₀` provides a
preimage. Injectivity follows from monodromy: for any path from `p e₀` to `p e₁` the monodromy
is a bijection `p ⁻¹' {p e₀} ≃ p ⁻¹' {p e₁}` (`IsCoveringMap.monodromy_bijective`), so the
singleton fiber over `p e₀` forces the fiber over `p e₁` to be a singleton as well. -/
theorem bijective_of_isCoveringMap_singleton_fiber {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) [PathConnectedSpace X]
    {e₀ : E} (h : p ⁻¹' {p e₀} = {e₀}) : Function.Bijective p := by
  refine ⟨?_, ?_⟩
  · intro e₁ e₂ he
    -- The fiber over `p e₀` is a singleton, hence a subsingleton.
    haveI : Subsingleton ↥(p ⁻¹' {p e₀}) := by rw [h]; infer_instance
    -- Monodromy along any path from `p e₀` to `p e₁` is a bijection of fibers.
    let γ : Path.Homotopic.Quotient (p e₀) (p e₁) :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (p e₀) (p e₁))
    have hbij : Function.Bijective (cov.monodromy γ) := cov.monodromy_bijective γ
    -- So the fiber over `p e₁` is a subsingleton too.
    haveI : Subsingleton ↥(p ⁻¹' {p e₁}) := hbij.surjective.subsingleton
    have hs : (⟨e₁, rfl⟩ : ↥(p ⁻¹' {p e₁})) = ⟨e₂, he.symm⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hs
  · intro x
    obtain ⟨y, hy⟩ := cov.comp_subtypeVal_pathComponent_surjective e₀ x
    exact ⟨y, hy⟩

end Work.SeedDyn
