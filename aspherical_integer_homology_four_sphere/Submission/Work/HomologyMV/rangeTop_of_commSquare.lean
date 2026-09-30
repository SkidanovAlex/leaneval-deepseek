import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-- Surjectivity is unchanged by linear equivalences in a commutative square: if `d (eM x) = eN (w x)` for all `x`, with `eM`, `eN` linear equivalences, and `w` is surjective, then `d` is surjective. -/
theorem rangeTop_of_commSquare {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M] [Module ℤ N] [Module ℤ M'] [Module ℤ N'] (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (d : M' →ₗ[ℤ] N') (w : M →ₗ[ℤ] N) (hsq : ∀ x, d (eM x) = eN (w x)) (hw : w.range = ⊤) : d.range = ⊤ := by
  rw [LinearMap.range_eq_top] at hw ⊢
  intro y
  obtain ⟨z, rfl⟩ := eN.surjective y
  obtain ⟨x, rfl⟩ := hw z
  exact ⟨eM x, hsq x⟩

end Work.HomologyMV
