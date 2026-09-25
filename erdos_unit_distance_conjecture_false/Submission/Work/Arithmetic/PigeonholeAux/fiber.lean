import Mathlib

namespace Work.Arithmetic.PigeonholeAux

theorem fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β)
    (hα : 0 < Fintype.card α) :
    ∃ a : α, Fintype.card α ≤ (Finset.univ.filter (fun a' => f a' = f a)).card * Fintype.card β := by
  obtain ⟨a₀⟩ := Fintype.card_pos_iff.mp hα
  have hsum : Fintype.card α = ∑ b : β, (Finset.univ.filter (fun a' => f a' = b)).card := by
    simpa using Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset β)) (f := f) (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  obtain ⟨b, -, hble⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset β))
    (f := fun _ => Fintype.card α)
    (g := fun b => (Finset.univ.filter (fun a' => f a' = b)).card * Fintype.card β)
    ⟨f a₀, Finset.mem_univ _⟩ (by
      have h' : (∑ b : β, (Finset.univ.filter (fun a' => f a' = b)).card * Fintype.card β)
          = ∑ _b : β, Fintype.card α := by
        rw [← Finset.sum_mul, ← hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_id, mul_comm]
      exact h'.ge)
  obtain ⟨a, ha⟩ : (Finset.univ.filter (fun a' => f a' = b)).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.card_empty, Nat.zero_mul] at hble
    omega
  refine ⟨a, ?_⟩
  rw [Finset.mem_filter] at ha
  rw [ha.2]
  exact hble

end Work.Arithmetic.PigeonholeAux
