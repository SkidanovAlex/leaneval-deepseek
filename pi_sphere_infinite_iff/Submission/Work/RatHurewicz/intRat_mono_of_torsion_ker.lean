import Mathlib
import Submission.Work.StemsB.RatBaseNaturality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Kernel-torsion implies rational injectivity of the base change `ℤ → ℚ`

Let `φ : A ⟶ B` be a morphism of `ℤ`-modules whose kernel is a torsion group, i.e. every
`a` with `φ a = 0` has `N • a = 0` for some `N > 0`.  Then tensoring `φ` with `ℚ` (the base
change `ModuleCat.extendScalars (Int.castRingHom ℚ)`, here `Work.StemsB.RatBC.IntRat`) is
injective, i.e. a monomorphism in `ModuleCat ℚ`.

The proof has two ingredients.

* `ℚ ⊗[ℤ] K` is a subsingleton for every torsion `ℤ`-module `K`
  (`subsingleton_tensorRat_of_torsion`): if `n • m = 0` with `n > 0` then for every `q : ℚ`
  `q ⊗ₜ m = (n • (q / n)) ⊗ₜ m = (q / n) ⊗ₜ (n • m) = 0`, and the pure tensors generate.
* `ℚ` is flat over `ℤ`, so `lTensor ℚ` of an injective linear map is injective, and
  `lTensor` is right exact.  Writing `φ = ψ ∘ (ker φ).mkQ` with `ψ` injective, the kernel of
  `lTensor ℚ φ` is the image of `lTensor ℚ (ker φ).subtype`, which is `0` because
  `ℚ ⊗[ℤ] ker φ` is a subsingleton.

Note on implementation: over `ℤ` the instance `AddCommGroup.toIntModule` competes with the
canonical `Submodule.module` structure, making the tensor products of submodules and quotients
not syntactically match the ones occurring in `Submodule.subtype`/`Submodule.mkQ`.  Removing
that redundant instance for the duration of the proof resolves the diamond.
-/

namespace Work.RatHurewicz

open CategoryTheory TensorProduct

/-- If every element of the `ℤ`-module `M` is torsion, then `ℚ ⊗[ℤ] M` is a subsingleton. -/
private theorem subsingleton_tensorRat_of_torsion {M : Type*} [AddCommGroup M] [Module ℤ M]
    (h : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n • m = 0) : Subsingleton (TensorProduct ℤ ℚ M) := by
  refine ⟨fun x y => ?_⟩
  suffices ∀ z : TensorProduct ℤ ℚ M, z = 0 by rw [this x, this y]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul q m =>
    obtain ⟨n, hnpos, hn⟩ := h m
    have hq : n • (q / n) = q := by
      rw [nsmul_eq_mul]; field_simp
    calc q ⊗ₜ[ℤ] m = (n • (q / n)) ⊗ₜ[ℤ] m := by rw [hq]
      _ = (q / n) ⊗ₜ[ℤ] (n • m) := TensorProduct.smul_tmul n (q / n) m
      _ = 0 := by rw [hn, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

attribute [-instance] AddCommGroup.toIntModule in
theorem intRat_mono_of_torsion_ker {A B : ModuleCat ℤ} (φ : A ⟶ B)
    (h : ∀ a : ↥A, φ.hom a = 0 → ∃ N : ℕ, 0 < N ∧ N • a = 0) :
    CategoryTheory.Mono (Work.StemsB.RatBC.IntRat.map φ) := by
  rw [ModuleCat.mono_iff_injective]
  show Function.Injective ⇑(LinearMap.lTensor ℚ (ModuleCat.Hom.hom φ))
  set K : Submodule ℤ ↥A := LinearMap.ker φ.hom with hK
  -- every element of the kernel is torsion
  have hKtors : ∀ k : ↥K, ∃ n : ℕ, 0 < n ∧ n • k = 0 := by
    intro k
    obtain ⟨n, hnpos, hn⟩ := h (k : ↥A) k.2
    exact ⟨n, hnpos, Subtype.ext (by simpa using hn)⟩
  have hsub : Subsingleton (TensorProduct ℤ ℚ ↥K) := subsingleton_tensorRat_of_torsion hKtors
  -- hence `ℚ ⊗ K → ℚ ⊗ A` is the zero map
  have hzero : LinearMap.lTensor ℚ (Submodule.subtype K) = 0 := by
    apply LinearMap.ext
    intro z
    have hz : z = 0 := Subsingleton.elim z 0
    simp [hz]
  -- and so the quotient map `A → A ⧸ K` stays injective after tensoring with `ℚ`
  have hmkQ : Function.Injective (LinearMap.lTensor ℚ K.mkQ) := by
    rw [← LinearMap.ker_eq_bot, lTensor_mkQ ℚ K, hzero, LinearMap.range_zero]
  -- `φ` factors through the quotient by its kernel, and the remaining map is injective,
  -- so flatness of `ℚ` keeps it injective after `lTensor ℚ`
  have hle : K ≤ (φ.hom).ker := le_of_eq hK
  set ψ : (↥A ⧸ K) →ₗ[ℤ] ↥B := K.liftQ φ.hom hle with hψ
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, hψ]
    exact Submodule.ker_liftQ_eq_bot K φ.hom hle (le_of_eq hK.symm)
  have hψT : Function.Injective (LinearMap.lTensor ℚ ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ hψinj
  have hcomp : LinearMap.lTensor ℚ φ.hom =
      (LinearMap.lTensor ℚ ψ).comp (LinearMap.lTensor ℚ K.mkQ) := by
    rw [← Submodule.liftQ_mkQ K φ.hom hle, LinearMap.lTensor_comp]
  rw [hcomp]
  exact hψT.comp hmkQ

end Work.RatHurewicz
