import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_comap_linearEquiv
import Submission.Commons.LinearAlgebra.Submodule.card_inf_bot_pairs

namespace Commons.LinearAlgebra.Submodule

open Module
set_option autoImplicit false

/-- **Exactly half of the `e` making `L` transversal to `comap e K` also make `L'` transversal**,
when `L, L'` are adjacent vertices of the Grassmann graph (`finrank (L ⊓ L') = ℓ - 1`) and
`L, L'` have dimension `ℓ ≤ finrank E`.

Proof route: by the fibre decomposition of `e ↦ comap e K`, both counts are the corresponding
counts of `(finrank K)`-dimensional subspaces `D` with `D ⊓ L = ⊥` (resp. also `D ⊓ L' = ⊥`),
multiplied by the common fibre size `κ = Nat.card {e // comap e K = K}`; so it suffices to show
`2 * #{D // finrank D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' = ⊥} = #{D // finrank D = k - ℓ ∧ D ⊓ L = ⊥}`,
which is `Commons.LinearAlgebra.Submodule.card_inf_bot_pairs`. -/
theorem two_mul_card_inf_comap (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k)
    (K : Submodule (ZMod 2) (Fin k → ZMod 2)) (hK : Module.finrank (ZMod 2) K = k - ℓ)
    (L L' : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hL : Module.finrank (ZMod 2) L = ℓ) (hL' : Module.finrank (ZMod 2) L' = ℓ)
    (hadj : Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1) :
    2 * Nat.card {e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) //
        L ⊓ Submodule.comap (e : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) K = ⊥ ∧
        L' ⊓ Submodule.comap (e : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) K = ⊥}
      = Nat.card {e : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2) //
        L ⊓ Submodule.comap (e : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) K = ⊥} := by
  classical
  -- The subspace-level count `card_inf_bot_pairs`.
  have hcp := card_inf_bot_pairs k ℓ hℓ hℓk L L' hL hL' hadj
  -- Rewrite the `k - ℓ` in `card_inf_bot_pairs` as `finrank K` and commute the infima.
  have hA : Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) K ∧ L ⊓ D = ⊥ ∧ L' ⊓ D = ⊥}
      = Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' = ⊥} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro D
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rwa [hK] at h1, by rw [inf_comm] at h2; exact h2,
        by rw [inf_comm] at h3; exact h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hK]; exact h1
      · rw [inf_comm]; exact h2
      · rw [inf_comm]; exact h3
  have hB : Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) K ∧ L ⊓ D = ⊥}
      = Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro D
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hK] at h1, by rw [inf_comm] at h2; exact h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [hK]; exact h1
      · rw [inf_comm]; exact h2
  have hAB : 2 * Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) K ∧ L ⊓ D = ⊥ ∧ L' ⊓ D = ⊥}
      = Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) K ∧ L ⊓ D = ⊥} := by
    rw [hA, hB]
    exact hcp
  -- The two fibre decompositions.
  have h1 := card_comap_linearEquiv (E := Fin k → ZMod 2) K (fun D => L ⊓ D = ⊥)
  have h2 := card_comap_linearEquiv (E := Fin k → ZMod 2) K
    (fun D => L ⊓ D = ⊥ ∧ L' ⊓ D = ⊥)
  rw [h2, h1]
  rw [← hAB]
  ring

end Commons.LinearAlgebra.Submodule
