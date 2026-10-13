import Mathlib
import Submission.Work.WilE9.Sharp.Clear

namespace Work.WilE9.Sharp

open MvPolynomial

/-- Degree bound for a single summand of `clearNumDen`: the term attached to a monomial `m` of `P`
has total degree at most `deg m + K * #β`, since each of the `β`-factors
`X (num b) ^ (m (inl b)) * X (den b) ^ (K - m (inl b))` contributes at most `m (inl b) + K`. -/
private lemma term_totalDegree_le {β γ α : Type*} [Fintype β] [Fintype γ]
    (num den : β → α) (ρ : γ → α) (K : ℕ) (m : β ⊕ γ →₀ ℕ) (c₀ : ℝ) :
    (MvPolynomial.C c₀ *
        (∏ b : β, MvPolynomial.X (num b) ^ (m (Sum.inl b)) *
          MvPolynomial.X (den b) ^ (K - m (Sum.inl b))) *
        (∏ c : γ, MvPolynomial.X (ρ c) ^ (m (Sum.inr c)))).totalDegree ≤
      (m.sum fun _ e => e) + K * Fintype.card β := by
  classical
  set A : MvPolynomial α ℝ :=
    ∏ b : β, MvPolynomial.X (num b) ^ (m (Sum.inl b)) *
      MvPolynomial.X (den b) ^ (K - m (Sum.inl b)) with hA_def
  set B : MvPolynomial α ℝ :=
    ∏ c : γ, MvPolynomial.X (ρ c) ^ (m (Sum.inr c)) with hB_def
  have hA : A.totalDegree ≤ ∑ b : β, (m (Sum.inl b) + K) := by
    rw [hA_def]
    refine le_trans (MvPolynomial.totalDegree_finsetProd Finset.univ _) ?_
    apply Finset.sum_le_sum
    intro b _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]
    omega
  have hB : B.totalDegree ≤ ∑ c : γ, m (Sum.inr c) := by
    rw [hB_def]
    refine le_trans (MvPolynomial.totalDegree_finsetProd Finset.univ _) (le_of_eq ?_)
    simp [MvPolynomial.totalDegree_X_pow]
  have hA2 : (MvPolynomial.C c₀ * A).totalDegree ≤ ∑ b : β, (m (Sum.inl b) + K) := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hA
  have hAB : (MvPolynomial.C c₀ * A * B).totalDegree
      ≤ (∑ b : β, (m (Sum.inl b) + K)) + (∑ c : γ, m (Sum.inr c)) :=
    le_trans (MvPolynomial.totalDegree_mul _ _) (add_le_add hA2 hB)
  have hsum : (∑ b : β, (m (Sum.inl b) + K))
      = (∑ b : β, m (Sum.inl b)) + K * Fintype.card β := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]
    simp
  have hsplit : (∑ b : β, m (Sum.inl b)) + (∑ c : γ, m (Sum.inr c))
      = m.sum (fun _ e => e) := by
    rw [← Fintype.sum_sum_type (fun i => m i)]
    exact (Finsupp.sum_fintype m (fun _ e => e) (fun i => rfl)).symm
  calc (MvPolynomial.C c₀ * A * B).totalDegree
      ≤ (∑ b : β, (m (Sum.inl b) + K)) + (∑ c : γ, m (Sum.inr c)) := hAB
    _ = ((∑ b : β, m (Sum.inl b)) + K * Fintype.card β) + (∑ c : γ, m (Sum.inr c)) := by
        rw [hsum]
    _ = ((∑ b : β, m (Sum.inl b)) + (∑ c : γ, m (Sum.inr c))) + K * Fintype.card β := by omega
    _ = (m.sum fun _ e => e) + K * Fintype.card β := by rw [hsplit]

theorem clearNumDen_totalDegree_le {β γ α : Type*} [Fintype β] [Fintype γ]
    (num den : β → α) (ρ : γ → α) (K : ℕ) (P : MvPolynomial (β ⊕ γ) ℝ) :
    (Work.WilE9.Sharp.clearNumDen num den ρ K P).totalDegree ≤
      K * Fintype.card β + P.totalDegree := by
  classical
  unfold Work.WilE9.Sharp.clearNumDen
  refine MvPolynomial.totalDegree_finsetSum_le (fun m hm => ?_)
  calc ((MvPolynomial.C (P.coeff m) *
        (∏ b : β, MvPolynomial.X (num b) ^ (m (Sum.inl b)) *
          MvPolynomial.X (den b) ^ (K - m (Sum.inl b))) *
        (∏ c : γ, MvPolynomial.X (ρ c) ^ (m (Sum.inr c)))).totalDegree)
      ≤ (m.sum fun _ e => e) + K * Fintype.card β :=
        term_totalDegree_le num den ρ K m (P.coeff m)
    _ ≤ P.totalDegree + K * Fintype.card β :=
        Nat.add_le_add_right (MvPolynomial.le_totalDegree hm) _
    _ = K * Fintype.card β + P.totalDegree := Nat.add_comm _ _

end Work.WilE9.Sharp
