import Mathlib

namespace Work.Repel

/-- Given finite sets `S₂ : Finset (ℕ × ℤ)` and `T : Finset ℤ` whose cardinalities
dominate real numbers `A` and `B ≥ 0`, there is a finite set `S` of triples whose
cardinality dominates `A * B` and which projects into `S₂ × T`.  The witness is the
product `S₂ × T`, transported across the associativity equivalence of products. -/
theorem triple_cells {A B : ℝ} (hB : 0 ≤ B) {S₂ : Finset (ℕ × ℤ)} (hS₂ : A ≤ (S₂.card : ℝ))
    {T : Finset ℤ} (hT : B ≤ (T.card : ℝ)) :
    ∃ S : Finset (ℕ × ℤ × ℤ), A * B ≤ (S.card : ℝ) ∧
      ∀ q ∈ S, (q.1, q.2.1) ∈ S₂ ∧ q.2.2 ∈ T := by
  refine ⟨(S₂ ×ˢ T).map (Equiv.prodAssoc ℕ ℤ ℤ).toEmbedding, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_product]
    have h1 : A * B ≤ (S₂.card : ℝ) * B := mul_le_mul_of_nonneg_right hS₂ hB
    have h2 : (S₂.card : ℝ) * B ≤ (S₂.card : ℝ) * (T.card : ℝ) :=
      mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)
    have h3 : ((S₂.card * T.card : ℕ) : ℝ) = (S₂.card : ℝ) * (T.card : ℝ) := by
      push_cast
      ring
    linarith
  · intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨p, hp, hpq⟩ := hq
    rw [Finset.mem_product] at hp
    rw [← hpq]
    exact ⟨by simpa [Equiv.prodAssoc] using hp.1, by simpa [Equiv.prodAssoc] using hp.2⟩

end Work.Repel
