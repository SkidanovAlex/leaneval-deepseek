import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-- Kernels are unchanged by linear equivalences in a commutative square: if `d (eM x) = eN (w x)` for all `x`, with `eM`, `eN` linear equivalences, then `ker d ≃ ker w`. -/
theorem kerIso_of_commSquare {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M] [Module ℤ N] [Module ℤ M'] [Module ℤ N'] (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (d : M' →ₗ[ℤ] N') (w : M →ₗ[ℤ] N) (hsq : ∀ x, d (eM x) = eN (w x)) : Nonempty (d.ker ≃ₗ[ℤ] w.ker) := by
  have h1 : ∀ x : M, w x = 0 → d (eM x) = 0 := by
    intro x hx; rw [hsq x, hx, map_zero]
  have h2 : ∀ y : M', d y = 0 → w (eM.symm y) = 0 := by
    intro y hy
    have h := hsq (eM.symm y)
    rw [eM.apply_symm_apply, hy] at h
    exact (eN.map_eq_zero_iff).mp h.symm
  exact ⟨{ toFun := fun y => ⟨eM.symm y, by rw [LinearMap.mem_ker]; exact h2 y y.2⟩
           invFun := fun x => ⟨eM x, by rw [LinearMap.mem_ker]; exact h1 x x.2⟩
           left_inv := by intro y; ext; exact eM.apply_symm_apply y
           right_inv := by intro x; ext; exact eM.symm_apply_apply x
           map_add' := by intro x y; ext; simp
           map_smul' := by intro c x; ext; simp }⟩

end Work.HomologyMV
