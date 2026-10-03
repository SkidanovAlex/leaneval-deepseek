import Mathlib

namespace Work.Peluse.LadderA

/-- **Density increment / Markov step.**  If `X : A × B → [0,1]` has total mass at least
`γ|A||B|`, then the set of rows `a` whose row average is at least `γ/2` has density at least `γ/2`
in `A` (the sum over `A` of the `0/1`-indicator of that set is at least `γ|A|/2`).

Proof.  Let `m a = |B|⁻¹ ∑_{b∈B} X a b` be the row average and let `T` be the `0/1` sum of the
rows with `m a ≥ γ/2`.  Each row satisfies the pointwise bound
`m a ≤ γ/2 + t a * (1 - γ/2)`, where `t a ∈ {0,1}` is the indicator of `m a ≥ γ/2`:  if `t a = 1`
then `m a ≤ 1` because every entry of `X` is `≤ 1`, and otherwise `m a < γ/2`.  Summing over `a`
and using `∑_a m a = |B|⁻¹ ∑_a ∑_b X a b ≥ |A| γ` (the hypothesis) gives
`|A| γ ≤ |A| (γ/2) + T (1 - γ/2)`, so `|A| γ/2 ≤ T (1 - γ/2) ≤ T` because `1 - γ/2 ≤ 1` and
`T ≥ 0`.  Dividing by `|A| > 0` yields the claim. -/
theorem markov_density {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (X : α → β → ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h0 : ∀ a ∈ A, ∀ b ∈ B, 0 ≤ X a b) (h1 : ∀ a ∈ A, ∀ b ∈ B, X a b ≤ 1) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : γ ≤ (A.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, X a b) :
    γ / 2 ≤ (A.card : ℝ)⁻¹ *
      ∑ a ∈ A, (if γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b then (1 : ℝ) else 0) := by
  have hAcard : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hBcard : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
  set T : ℝ := ∑ a ∈ A, (if γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b then (1 : ℝ) else 0) with hT
  -- Pointwise bound on each row average.
  have hterm : ∀ a ∈ A, (B.card : ℝ)⁻¹ * (∑ b ∈ B, X a b)
      ≤ γ / 2 + (if γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b then (1 : ℝ) else 0) * (1 - γ / 2) := by
    intro a ha
    by_cases h : γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b
    · rw [if_pos h]
      have hsum_le : ∑ b ∈ B, X a b ≤ (B.card : ℝ) := by
        calc ∑ b ∈ B, X a b ≤ ∑ b ∈ B, (1 : ℝ) := Finset.sum_le_sum (fun b hb => h1 a ha b hb)
          _ = (B.card : ℝ) := by simp
      have h1' : (B.card : ℝ)⁻¹ * (∑ b ∈ B, X a b) ≤ 1 := by
        have h2 := mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (le_of_lt hBcard))
        rwa [inv_mul_cancel₀ (ne_of_gt hBcard)] at h2
      linarith
    · rw [if_neg h]
      have hlt : (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b < γ / 2 := lt_of_not_ge h
      linarith
  -- Sum the pointwise bound over the rows.
  have hsum_le : ∑ a ∈ A, (B.card : ℝ)⁻¹ * (∑ b ∈ B, X a b)
      ≤ ∑ a ∈ A, (γ / 2 + (if γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b then (1 : ℝ) else 0) * (1 - γ / 2)) :=
    Finset.sum_le_sum hterm
  have hleft : ∑ a ∈ A, (B.card : ℝ)⁻¹ * (∑ b ∈ B, X a b)
      = (B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, X a b := by
    rw [Finset.mul_sum]
  have h1s : ∑ a ∈ A, (γ / 2 : ℝ) = (A.card : ℝ) * (γ / 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2s : ∑ a ∈ A, (if γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b then (1 : ℝ) else 0) * (1 - γ / 2)
      = T * (1 - γ / 2) := by
    rw [← Finset.sum_mul, ← hT]
  have hsplit : ∑ a ∈ A, (γ / 2 + (if γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b then (1 : ℝ) else 0) * (1 - γ / 2))
      = (A.card : ℝ) * (γ / 2) + T * (1 - γ / 2) := by
    rw [Finset.sum_add_distrib, h1s, h2s]
  -- The hypothesis, cleared of the `|A|⁻¹` and rewritten as a sum of row averages.
  have hγA : (A.card : ℝ) * γ ≤ ∑ a ∈ A, (B.card : ℝ)⁻¹ * (∑ b ∈ B, X a b) := by
    have h1 : γ ≤ (A.card : ℝ)⁻¹ * ((B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, X a b) := by
      have h := hγ; rw [mul_assoc] at h; exact h
    have h2 : (A.card : ℝ) * γ ≤ (B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, X a b := by
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hAcard)
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hAcard), one_mul] at h3
    rw [hleft]
    exact h2
  have hchain : (A.card : ℝ) * γ ≤ (A.card : ℝ) * (γ / 2) + T * (1 - γ / 2) :=
    le_trans hγA (le_trans hsum_le (le_of_eq hsplit))
  have hT_nonneg : 0 ≤ T := by
    rw [hT]
    exact Finset.sum_nonneg (fun a ha => by by_cases h : γ / 2 ≤ (B.card : ℝ)⁻¹ * ∑ b ∈ B, X a b <;> simp [h])
  have hhalf : (A.card : ℝ) * (γ / 2) ≤ T := by
    have hle1 : T * (1 - γ / 2) ≤ T := mul_le_of_le_one_right hT_nonneg (by linarith)
    nlinarith [hchain, hle1]
  have hfin : γ / 2 ≤ (A.card : ℝ)⁻¹ * T := by
    have h := mul_le_mul_of_nonneg_left hhalf (inv_nonneg.mpr (le_of_lt hAcard))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hAcard), one_mul] at h
  exact hfin

end Work.Peluse.LadderA
