import Mathlib

namespace Work.NN.Newton

/-- Abstract arithmetic core of one Newton step: for a constant `C` that dominates `1`, `C₄ C₅`,
`2 C₄` and `C₅ (1 + 2 C₄)`, the Newton-step quantities satisfy the required bounds. -/
private lemma newtonStepConsts_key {C₄ C₅ C : ℝ} (h₄ : 0 < C₄) (h₅ : 0 < C₅)
    (hCpos : 0 < C) (hC1 : 1 ≤ C) (hC45 : C₄ * C₅ ≤ C) (hC24 : 2 * C₄ ≤ C)
    (hC5 : C₅ * (1 + 2 * C₄) ≤ C) (N₄ : ℕ) :
    ∀ δ a : ℝ, 0 < δ → δ ≤ 1 / 8 → 0 ≤ a → a ≤ δ ^ (N₄ + 1) / C →
        a ≤ 1 ∧ 0 ≤ C₄ / δ ^ N₄ * a ∧ C₄ / δ ^ N₄ * a ≤ δ / C₅ ∧ C₄ / δ ^ N₄ * a < 1 ∧
        C₄ / δ ^ N₄ * a ≤ C / δ ^ (N₄ + 1) * a ∧ 0 ≤ C₄ / δ ^ N₄ * a ^ 2 ∧
        C₅ * (a ^ 2 + C₄ / δ ^ N₄ * a ^ 2 + a * (C₄ / δ ^ N₄ * a))
          ≤ C / δ ^ (N₄ + 1) * a ^ 2 := by
  intro δ a hδ hδ8 ha hbound
  have hδ1 : δ ≤ 1 := by linarith
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hδNpos : 0 < δ ^ N₄ := pow_pos hδ N₄
  have hδpow1 : δ ^ (N₄ + 1) ≤ 1 := pow_le_one₀ hδ0 hδ1
  have hδN1 : δ ^ N₄ ≤ 1 := pow_le_one₀ hδ0 hδ1
  have hδsucc : δ ^ (N₄ + 1) = δ ^ N₄ * δ := pow_succ δ N₄
  have hAp : 0 ≤ C₄ / δ ^ N₄ := div_nonneg (le_of_lt h₄) (le_of_lt hδNpos)
  have hbound' : a ≤ δ ^ N₄ * δ / C := by
    have := hbound; rw [hδsucc] at this; exact this
  have h1 : a ≤ 1 := by
    have : δ ^ (N₄ + 1) / C ≤ 1 := (div_le_one hCpos).mpr (by linarith [hδpow1, hC1])
    linarith [hbound, this]
  have h2 : 0 ≤ C₄ / δ ^ N₄ * a := mul_nonneg hAp ha
  have heq : C₄ / δ ^ N₄ * (δ ^ N₄ * δ / C) = C₄ * δ / C := by
    field_simp
  have hs3 : C₄ / δ ^ N₄ * a ≤ C₄ * δ / C :=
    (mul_le_mul_of_nonneg_left hbound' hAp).trans heq.le
  have h3 : C₄ / δ ^ N₄ * a ≤ δ / C₅ := by
    have hle : C₄ * δ / C ≤ δ / C₅ := by
      rw [div_le_div_iff₀ hCpos h₅]
      nlinarith [hC45, hδ0, le_of_lt h₄]
    linarith [hs3, hle]
  have h4 : C₄ / δ ^ N₄ * a < 1 := by
    have hle1 : C₄ * δ / C ≤ C₄ / C := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hCpos)
      nlinarith [le_of_lt h₄, hδ1]
    have hlt : C₄ / C < 1 := by
      rw [div_lt_one hCpos]
      linarith [hC24, h₄]
    linarith [hs3, hle1, hlt]
  have h5 : C₄ / δ ^ N₄ * a ≤ C / δ ^ (N₄ + 1) * a := by
    have hcoef : C₄ / δ ^ N₄ ≤ C / δ ^ (N₄ + 1) := by
      rw [div_le_div_iff₀ hδNpos (pow_pos hδ (N₄ + 1))]
      rw [hδsucc]
      have hCs : C₄ * δ ≤ C := by nlinarith [hC24, hδ1, h₄]
      have := mul_le_mul_of_nonneg_right hCs (le_of_lt hδNpos)
      nlinarith [this]
    exact mul_le_mul_of_nonneg_right hcoef ha
  have h6 : 0 ≤ C₄ / δ ^ N₄ * a ^ 2 := mul_nonneg hAp (sq_nonneg a)
  have h7 : C₅ * (a ^ 2 + C₄ / δ ^ N₄ * a ^ 2 + a * (C₄ / δ ^ N₄ * a))
      ≤ C / δ ^ (N₄ + 1) * a ^ 2 := by
    have hkey : C₅ * δ * (δ ^ N₄ + 2 * C₄) ≤ C := by
      have h1' : δ * (δ ^ N₄ + 2 * C₄) ≤ 1 + 2 * C₄ := by nlinarith [hδ1, hδN1, h₄]
      have h2' : C₅ * (δ * (δ ^ N₄ + 2 * C₄)) ≤ C₅ * (1 + 2 * C₄) :=
        mul_le_mul_of_nonneg_left h1' (le_of_lt h₅)
      nlinarith [h2', hC5]
    have hA : C₅ * (1 + 2 * (C₄ / δ ^ N₄)) ≤ C / δ ^ (N₄ + 1) := by
      have htmp : C₅ * (1 + 2 * (C₄ / δ ^ N₄)) * δ ^ N₄ ≤ C / δ ^ (N₄ + 1) * δ ^ N₄ := by
        have e1 : C₅ * (1 + 2 * (C₄ / δ ^ N₄)) * δ ^ N₄ = C₅ * (δ ^ N₄ + 2 * C₄) := by
          field_simp
        have e2 : C / δ ^ (N₄ + 1) * δ ^ N₄ = C / δ := by
          rw [hδsucc]; field_simp
        rw [e1, e2]
        rw [le_div_iff₀ hδ]
        nlinarith [hkey]
      exact (mul_le_mul_iff_of_pos_right hδNpos).mp htmp
    have hsum : a ^ 2 + C₄ / δ ^ N₄ * a ^ 2 + a * (C₄ / δ ^ N₄ * a)
        = (1 + 2 * (C₄ / δ ^ N₄)) * a ^ 2 := by ring
    rw [hsum]
    calc C₅ * ((1 + 2 * (C₄ / δ ^ N₄)) * a ^ 2)
        = C₅ * (1 + 2 * (C₄ / δ ^ N₄)) * a ^ 2 := by ring
      _ ≤ C / δ ^ (N₄ + 1) * a ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg a)
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **Arithmetic of one Newton step.**  Given the constants `C₄, C₅ > 0` of the correction and
push-forward steps and the exponent `N₄` of the correction step, there is `C > 0` such that with
`N = N₄ + 1`, whenever `1 ≤ r ≤ 4`, `0 < δ ≤ 1/8` and `0 ≤ a ≤ δ^N / C`, the numbers
`b = C₄ δ^{-N₄} a` and `e = C₄ δ^{-N₄} a²` satisfy `a ≤ 1`, `b ≥ 0`, `b ≤ δ/C₅`, `b < 1`,
`b ≤ C δ^{-N} a`, `e ≥ 0` and `C₅ (a² + e + a b) ≤ C δ^{-N} a²`. -/
theorem newtonStepConsts {C₄ C₅ : ℝ} (h₄ : 0 < C₄) (h₅ : 0 < C₅) (N₄ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r δ a : ℝ, 1 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 8 → 0 ≤ a →
      a ≤ δ ^ (N₄ + 1) / C →
        a ≤ 1 ∧ 0 ≤ C₄ / δ ^ N₄ * a ∧ C₄ / δ ^ N₄ * a ≤ δ / C₅ ∧ C₄ / δ ^ N₄ * a < 1 ∧
        C₄ / δ ^ N₄ * a ≤ C / δ ^ (N₄ + 1) * a ∧ 0 ≤ C₄ / δ ^ N₄ * a ^ 2 ∧
        C₅ * (a ^ 2 + C₄ / δ ^ N₄ * a ^ 2 + a * (C₄ / δ ^ N₄ * a))
          ≤ C / δ ^ (N₄ + 1) * a ^ 2 := by
  refine ⟨C₄ * C₅ + 2 * C₄ + C₅ * (1 + 2 * C₄) + 2, ?_, ?_⟩
  · nlinarith [h₄, h₅, mul_pos h₄ h₅]
  · intro r δ a hr1 hr4 hδ hδ8 ha hbound
    exact newtonStepConsts_key h₄ h₅ (by nlinarith [h₄, h₅, mul_pos h₄ h₅])
      (by nlinarith [h₄, h₅]) (by nlinarith [h₄, h₅]) (by nlinarith [h₄, h₅])
      (by nlinarith [h₄, h₅]) N₄ δ a hδ hδ8 ha hbound

end Work.NN.Newton
