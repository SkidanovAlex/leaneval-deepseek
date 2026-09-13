import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.exists_linearEquiv_pair

namespace Commons.LinearAlgebra.Submodule

open Module
set_option autoImplicit false

/-- **The `comap` of a composite on the right.** For linear automorphisms `e₀`, `e` of a
module `V` and a submodule `X`,
`comap (e₀.symm.trans e) X = map e₀ (comap e X)`. -/
lemma comap_symm_trans_eq_map_comap {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (e₀ e : V ≃ₗ[F] V) (X : Submodule F V) :
    Submodule.comap ((e₀.symm.trans e : V ≃ₗ[F] V) : V →ₗ[F] V) X
      = Submodule.map (e₀ : V →ₗ[F] V) (Submodule.comap (e : V →ₗ[F] V) X) := by
  rw [show ((e₀.symm.trans e : V ≃ₗ[F] V) : V →ₗ[F] V)
      = (e : V →ₗ[F] V).comp (e₀.symm : V →ₗ[F] V) from rfl]
  rw [Submodule.comap_comp]
  rw [Submodule.map_equiv_eq_comap_symm]

/-- **Transporting the transversality count along a linear automorphism.** If `e₀` carries `L`
onto `L'`, then the number of automorphisms `e` with `L ⊓ comap e K₀ = ⊥` equals the number
with `L' ⊓ comap e K₀ = ⊥`: right composition with `e₀⁻¹` is a bijection between the two
sets, since `map e₀` is an order isomorphism. -/
theorem natCard_subtype_inf_comap_eq_of_map_eq {F E : Type*} [Field F] [AddCommGroup E]
    [Module F E] (K₀ L L' : Submodule F E) (e₀ : E ≃ₗ[F] E)
    (hmap : L.map (e₀ : E →ₗ[F] E) = L') :
    Nat.card {e : E ≃ₗ[F] E // L ⊓ Submodule.comap (e : E →ₗ[F] E) K₀ = ⊥}
      = Nat.card {e : E ≃ₗ[F] E // L' ⊓ Submodule.comap (e : E →ₗ[F] E) K₀ = ⊥} := by
  classical
  have hcoe : ∀ e : E ≃ₗ[F] E, (Equiv.mulRight (e₀⁻¹) e : E ≃ₗ[F] E) = e₀.symm.trans e := by
    intro e
    rw [show Equiv.mulRight (e₀⁻¹) e = e * e₀⁻¹ from rfl]
    exact LinearEquiv.mul_eq_trans e e₀.symm
  have key : ∀ e : E ≃ₗ[F] E,
      (L ⊓ Submodule.comap (e : E →ₗ[F] E) K₀ = ⊥) ↔
        (L' ⊓ Submodule.comap ((Equiv.mulRight (e₀⁻¹) e : E ≃ₗ[F] E) : E →ₗ[F] E) K₀ = ⊥) := by
    intro e
    rw [hcoe e, comap_symm_trans_eq_map_comap, ← hmap]
    rw [← Submodule.map_inf (e₀ : E →ₗ[F] E) e₀.injective]
    exact (Submodule.map_eq_bot_iff (e := e₀)).symm
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight (e₀⁻¹)) key)

/-- **The number of `e` making `L` transversal to `comap e K` does not depend on `L`.**
By the fibre decomposition `Commons.LinearAlgebra.Submodule.card_comap_linearEquiv` (or
directly), both sides equal `κ * Nat.card {D // finrank D = finrank K ∧ D ⊓ L = ⊥}` with
`κ = Nat.card {e // comap e K = K}`, and the latter count is independent of `L` because any
two subspaces of the same dimension are related by a linear equivalence. -/
theorem card_L_inf_comap_eq {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]
    (K L L' : Submodule (ZMod 2) E)
    (hL : Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) K)
    (hL' : Module.finrank (ZMod 2) L' = Module.finrank (ZMod 2) K) :
    Nat.card {e : E ≃ₗ[ZMod 2] E // L ⊓ Submodule.comap (e : E →ₗ[ZMod 2] E) K = ⊥}
      = Nat.card {e : E ≃ₗ[ZMod 2] E // L' ⊓ Submodule.comap (e : E →ₗ[ZMod 2] E) K = ⊥} := by
  classical
  obtain ⟨e₀, hmap, -⟩ :=
    exists_linearEquiv_pair (V := E) L ⊥ L' ⊥ (by rw [hL, hL']) (by rw [finrank_bot])
      (by rw [inf_bot_eq, inf_bot_eq, finrank_bot])
  exact natCard_subtype_inf_comap_eq_of_map_eq K L L' e₀ hmap

end Commons.LinearAlgebra.Submodule
