import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory MonoidalCategory

/-- Any finitely generated `ℤ`-module fits into a short exact sequence with free terms of finite rank: take a surjection `ℤ^b ↠ M`; its kernel is a finitely generated submodule of a free module over the PID `ℤ`, hence free of finite rank. -/
theorem exists_shortExact_free (M : ModuleCat ℤ) (hM : Module.Finite ℤ M) :
    ∃ (P Q : ModuleCat ℤ) (f : P ⟶ Q) (g : Q ⟶ M) (h : f ≫ g = 0),
      Module.Free ℤ P ∧ Module.Finite ℤ P ∧ Module.Free ℤ Q ∧ Module.Finite ℤ Q ∧
      (ShortComplex.mk f g h).ShortExact := by
  classical
  -- A surjection from a finitely generated free module onto `M`.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ (M : Type _)
  -- Make it live in the same universe as `M`, using `ULift`.
  let e := ULift.moduleEquiv (R := ℤ) (M := (Fin n → ℤ))
  let g : ULift (Fin n → ℤ) →ₗ[ℤ] (M : Type _) := f.comp e.toLinearMap
  have hg : Function.Surjective g := hf.comp e.surjective
  -- `Q = ℤ^n` is free of finite rank, and its kernel `K = P` is free of finite rank
  -- by the structure theory of finitely generated modules over a PID.
  let K := LinearMap.ker g
  obtain ⟨_, bK⟩ := Submodule.basisOfPid (R := ℤ) (M := ULift (Fin n → ℤ))
    (Module.Free.chooseBasis ℤ (ULift (Fin n → ℤ))) K
  have hfreeK : Module.Free ℤ K := Module.Free.of_basis bK
  have hfinK : Module.Finite ℤ K := Module.Finite.of_basis bK
  let P : ModuleCat ℤ := ModuleCat.of ℤ K
  let Q : ModuleCat ℤ := ModuleCat.of ℤ (ULift (Fin n → ℤ))
  let f₀ : P ⟶ Q := ModuleCat.ofHom K.subtype
  let g₀ : Q ⟶ M := ModuleCat.ofHom g
  have h₀ : f₀ ≫ g₀ = 0 := by
    dsimp only [f₀, g₀]
    ext x
    simp only [ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, ModuleCat.hom_zero,
      LinearMap.comp_apply, LinearMap.zero_apply]
    exact x.2
  refine ⟨P, Q, f₀, g₀, h₀, hfreeK, hfinK,
    Module.Free.of_basis (Module.Free.chooseBasis ℤ (ULift (Fin n → ℤ))),
    Module.Finite.of_basis (Module.Free.chooseBasis ℤ (ULift (Fin n → ℤ))), ?_⟩
  -- `0 → K → ℤ^n → M → 0` is short exact.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    show LinearMap.range K.subtype = LinearMap.ker g
    rw [Submodule.range_subtype]
  · exact (ModuleCat.mono_iff_injective _).mpr K.injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr hg

end Work.SSS
