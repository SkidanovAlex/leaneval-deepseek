import Mathlib
import Submission.Commons.PeriodicTiling.functional_system_to_tiling_system

namespace Commons.PeriodicTiling.FunctionalSystem

theorem solve_pointwise_transport {G D : Type} [AddCommGroup G] [AddCommGroup D]
    {H : Type} [AddCommGroup H] (σ : G ≃+ D)
    (M : ℕ) (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H) (β : D → H)
    (hβ : ∀ (i : Fin M) (x : D) (y : H), ∃! j : Fin (J i), y ∈ β (x + σ (h i j)) + E i j) :
    ∀ (i : Fin M) (x : G) (y : H), ∃! j : Fin (J i), y ∈ β (σ (x + h i j)) + E i j := by
  intro i x y
  -- σ is additive, so σ (x + h i j) = σ x + σ (h i j); apply hβ at σ x.
  simpa [map_add] using hβ i (σ x) y

end Commons.PeriodicTiling.FunctionalSystem
