import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Additive.Gowers

/-- Permuting three nested finite sums: move the innermost index to the outside. -/
lemma sum_comm_three {α β γ M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (u : Finset γ) (f : α → β → γ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  have h1 : (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c)
      = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c := by
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [h1]
  exact Finset.sum_comm

theorem ap_count_prod_add {p : ℕ} [Fact p.Prime] (k : ℕ) (g h : ZMod p → ℝ) :
    (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k,
        (g (x + ((i : ℕ) : ZMod p) * r) + h (x + ((i : ℕ) : ZMod p) * r)))
      = ∑ t ∈ (Finset.univ : Finset (Fin k)).powerset,
          ∑ x : ZMod p, ∑ r : ZMod p,
            (∏ i ∈ t, g (x + ((i : ℕ) : ZMod p) * r)) *
              (∏ i ∈ tᶜ, h (x + ((i : ℕ) : ZMod p) * r)) := by
  simp only [Finset.compl_eq_univ_sdiff]
  simp_rw [Finset.prod_add]
  conv_lhs => rw [sum_comm_three]

end Commons.Combinatorics.Additive.Gowers