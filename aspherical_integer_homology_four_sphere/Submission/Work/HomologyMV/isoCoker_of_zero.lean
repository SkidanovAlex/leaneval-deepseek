import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-- If `M --f--> N --g--> X --h--> Y` is exact at `N` and at `X` and the last map `h` is zero, then `X ≅ coker f`.  This is the degree-`0` companion of `isoKer_of_surjective`. -/
theorem isoCoker_of_zero {M N X Y : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup X] [AddCommGroup Y] [Module ℤ M] [Module ℤ N] [Module ℤ X] [Module ℤ Y] (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] X) (h : X →ₗ[ℤ] Y) (hf : Function.Exact f g) (hg : Function.Exact g h) (hzero : h = 0) : Nonempty (X ≃ₗ[ℤ] N ⧸ f.range) := by
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.exact_zero_iff_surjective Y, ← hzero]
    exact hg
  rw [← hf.linearMap_ker_eq]
  have hmod : (Submodule.Quotient.module (LinearMap.ker g)) =
      (AddCommGroup.toIntModule (N ⧸ LinearMap.ker g)) := Subsingleton.elim _ _
  exact ⟨hmod ▸ (g.quotKerEquivOfSurjective hsurj).symm⟩

end Work.HomologyMV
