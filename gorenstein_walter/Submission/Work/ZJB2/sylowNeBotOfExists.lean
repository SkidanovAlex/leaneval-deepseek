import Mathlib

namespace Work.ZJB2

theorem sylowNeBotOfExists (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G]
    (hex : ∃ S : Sylow p G, (S : Subgroup G) ≠ ⊥) (S₂ : Sylow p G) : (S₂ : Subgroup G) ≠ ⊥ := by
  -- Every Sylow `p`-subgroup has the same order `p ^ (Nat.card G).factorization p`, so
  -- either all of them are trivial or none of them is.
  obtain ⟨S, hS⟩ := hex
  intro hbot
  apply hS
  have h1 : Nat.card ↥(S₂ : Subgroup G) = 1 := Subgroup.card_eq_one.mpr hbot
  have h2 : Nat.card ↥(S : Subgroup G) = 1 := by
    rw [Sylow.card_eq_multiplicity (P := S), Sylow.card_eq_multiplicity (P := S₂)] at *
    exact h1
  exact Subgroup.card_eq_one.mp h2

end Work.ZJB2
