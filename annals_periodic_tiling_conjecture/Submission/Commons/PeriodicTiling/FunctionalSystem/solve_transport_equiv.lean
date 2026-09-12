import Mathlib
import Submission.Commons.PeriodicTiling.functional_system_to_tiling_system

open scoped Pointwise

namespace Commons.PeriodicTiling.FunctionalSystem

/-- Transport of `∃!` along a pointwise iff of predicates. -/
lemma existsUnique_iff_congr {ι : Sort*} {p q : ι → Prop}
    (hpq : ∀ j, p j ↔ q j) : (∃! j, p j) ↔ (∃! j, q j) := by
  constructor
  · rintro ⟨j0, hj0, huniq⟩
    refine ⟨j0, (hpq j0).1 hj0, ?_⟩
    intro j hj
    exact huniq j ((hpq j).2 hj)
  · rintro ⟨j0, hj0, huniq⟩
    refine ⟨j0, (hpq j0).2 hj0, ?_⟩
    intro j hj
    exact huniq j ((hpq j).1 hj)

theorem solve_transport_equiv {G D : Type} [AddCommGroup G] [AddCommGroup D] {H : Type} [AddCommGroup H]
    (σ : G ≃+ D)
    (M : ℕ) (J : Fin M → ℕ) (h : (i : Fin M) → Fin (J i) → G)
    (E : (i : Fin M) → Fin (J i) → Set H) :
    (∃ α : G → H, ∀ (i : Fin M) (x : G) (y : H),
        ∃! j : Fin (J i), y ∈ α (x + h i j) + E i j) ↔
    (∃ β : D → H, ∀ (i : Fin M) (x : D) (y : H),
        ∃! j : Fin (J i), y ∈ β (x + σ (h i j)) + E i j) := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨fun d : D => α (σ.symm d), ?_⟩
    intro i x y
    have hx0 : ∀ j : Fin (J i),
        y ∈ α (σ.symm x + h i j) + E i j ↔
        y ∈ (fun d : D => α (σ.symm d)) (x + σ (h i j)) + E i j := by
      intro j
      change y ∈ α (σ.symm x + h i j) + E i j ↔
        y ∈ α (σ.symm (x + σ (h i j))) + E i j
      have harg : σ.symm (x + σ (h i j)) = σ.symm x + h i j := by
        rw [map_add]
        rw [σ.symm_apply_apply]
      rw [harg]
    rcases hα i (σ.symm x) y with ⟨j0, hj0, huniq⟩
    refine ⟨j0, (hx0 j0).1 hj0, ?_⟩
    intro j hj
    exact huniq j ((hx0 j).2 hj)
  · rintro ⟨β, hβ⟩
    refine ⟨fun z : G => β (σ z), ?_⟩
    intro i x y
    have hx0 : ∀ j : Fin (J i),
        y ∈ β (σ x + σ (h i j)) + E i j ↔
        y ∈ (fun z : G => β (σ z)) (x + h i j) + E i j := by
      intro j
      change y ∈ β (σ x + σ (h i j)) + E i j ↔
        y ∈ β (σ (x + h i j)) + E i j
      have harg : σ (x + h i j) = σ x + σ (h i j) := by
        rw [map_add]
      rw [harg]
    rcases hβ i (σ x) y with ⟨j0, hj0, huniq⟩
    refine ⟨j0, (hx0 j0).1 hj0, ?_⟩
    intro j hj
    exact huniq j ((hx0 j).2 hj)

end Commons.PeriodicTiling.FunctionalSystem
