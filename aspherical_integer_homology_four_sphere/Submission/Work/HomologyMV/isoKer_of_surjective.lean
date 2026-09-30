import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-- The engine of the Mayer–Vietoris computation: if `M --f--> N --g--> X --h--> Y --g'--> Z` is exact at `N`, at `X` and at `Y`, and `f` is surjective, then `X ≅ ker g'`. -/
theorem isoKer_of_surjective {M N X Y Z : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module ℤ M] [Module ℤ N] [Module ℤ X] [Module ℤ Y] [Module ℤ Z] (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] X) (h : X →ₗ[ℤ] Y) (g' : Y →ₗ[ℤ] Z) (hf : Function.Exact f g) (hg : Function.Exact g h) (hh : Function.Exact h g') (hsurj : f.range = ⊤) : Nonempty (X ≃ₗ[ℤ] g'.ker) := by
  -- Turn exactness into kernel = range.
  rw [LinearMap.exact_iff] at hf hg hh
  -- hf : g.ker = f.range, hg : h.ker = g.range, hh : g'.ker = h.range
  -- Since `f` is surjective, `g` vanishes.
  have hg_zero : g = 0 := by
    ext x
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (by rw [hf, hsurj]; trivial)
  -- Hence `h` is injective.
  have hker : h.ker = ⊥ := by
    rw [hg, hg_zero, LinearMap.range_zero]
  have hinj : Function.Injective h := LinearMap.ker_eq_bot.mp hker
  -- `h` corestricts to a bijection `X → ker g'`.
  let H := h.codRestrict g'.ker (fun x => by rw [hh]; exact LinearMap.mem_range_self h x)
  have hbij : Function.Bijective H := by
    constructor
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · intro y
      obtain ⟨x, hx⟩ := (show (y : Y) ∈ h.range by rw [← hh]; exact y.2)
      refine ⟨x, ?_⟩
      apply Subtype.ext
      rw [LinearMap.codRestrict_apply]
      exact hx
  let e := LinearEquiv.ofBijective H hbij
  -- `ℤ`-module structures on a type are unique, so the two possible module structures
  -- on the subtype `↥g'.ker` coincide; transport the equivalence across them.
  have hinst : (Submodule.module g'.ker : Module ℤ ↥g'.ker) = AddCommGroup.toIntModule ↥g'.ker :=
    Subsingleton.elim _ _
  exact ⟨Eq.mp (congrArg (fun I : Module ℤ ↥g'.ker =>
    @LinearEquiv ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _ X ↥g'.ker _ _ _ I) hinst) e⟩

end Work.HomologyMV
