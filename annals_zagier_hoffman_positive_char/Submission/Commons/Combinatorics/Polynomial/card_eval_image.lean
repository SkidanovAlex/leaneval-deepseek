import Mathlib
import Submission.Commons.Combinatorics.Polynomial.card_degreeLE

namespace Commons.Combinatorics.Polynomial

theorem card_eval_image {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    {θ : K} (hθ : ∀ p : Polynomial F, p.eval₂ (algebraMap F K) θ = 0 → p = 0) (n : ℕ) :
    Nat.card {x : K // ∃ p : Polynomial F, p.natDegree ≤ n ∧ p.eval₂ (algebraMap F K) θ = x}
      = (Nat.card F) ^ (n + 1) := by
  let φ : Polynomial.degreeLE F (n : WithBot ℕ) → K :=
    fun p => (p : Polynomial F).eval₂ (algebraMap F K) θ
  have hinj : Function.Injective φ := by
    intro p q hpq
    apply Subtype.ext
    have hpq' : (p : Polynomial F).eval₂ (algebraMap F K) θ
        = (q : Polynomial F).eval₂ (algebraMap F K) θ := hpq
    have hmem : (p : Polynomial F) - (q : Polynomial F) = 0 := by
      apply hθ
      rw [Polynomial.eval₂_sub, hpq', sub_self]
    exact sub_eq_zero.mp hmem
  have hpred : ∀ x : K,
      (∃ p : Polynomial F, p.natDegree ≤ n ∧ p.eval₂ (algebraMap F K) θ = x) ↔
      (∃ p : Polynomial.degreeLE F (n : WithBot ℕ), φ p = x) := by
    intro x
    constructor
    · rintro ⟨p, hdeg, heval⟩
      exact ⟨⟨p, Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hdeg)⟩, heval⟩
    · rintro ⟨p, hp⟩
      exact ⟨(p : Polynomial F), Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp p.2), hp⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hpred)]
  change Nat.card ↑(Set.range φ) = (Nat.card F) ^ (n + 1)
  rw [Nat.card_range_of_injective hinj]
  exact card_degreeLE F n

end Commons.Combinatorics.Polynomial
