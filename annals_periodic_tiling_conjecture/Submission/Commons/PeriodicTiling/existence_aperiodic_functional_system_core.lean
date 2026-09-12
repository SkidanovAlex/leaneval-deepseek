import Mathlib
import Submission.Commons.PeriodicTiling.functional_system_to_tiling_system
import Submission.Commons.PeriodicTiling.existence_aperiodic_functional_system_core_full

namespace Commons.PeriodicTiling

theorem existence_aperiodic_functional_system_core :
    ∃ (G₁ : Type) (_ : AddCommGroup G₁) (_ : Finite G₁),
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
    ∃ (M : ℕ) (J : Fin M → ℕ)
      (h : (i : Fin M) → Fin (J i) → (ℤ × ℤ × G₁))
      (E : (i : Fin M) → Fin (J i) → Set H),
      (∀ i j, (E i j).Nonempty) ∧
      (∃ α : (ℤ × ℤ × G₁) → H,
        ∀ i x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j) ∧
      ∀ α : (ℤ × ℤ × G₁) → H,
        (∀ i x y, ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j) →
        ¬ ∃ L : AddSubgroup (ℤ × ℤ × G₁), L.FiniteIndex ∧
          ∀ x : (ℤ × ℤ × G₁), ∀ g : (ℤ × ℤ × G₁), g ∈ L → α (x + g) = α x := by
  exact existence_aperiodic_functional_system_core_full

end Commons.PeriodicTiling
