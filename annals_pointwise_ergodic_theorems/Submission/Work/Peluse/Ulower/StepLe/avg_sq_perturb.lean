import Mathlib

namespace Work.Peluse.Ulower.StepLe

/-- Averaging/perturbation lemma.

If `a ≥ 0`, `b ≥ 0`, `b ≥ a - ε` pointwise on a nonempty finite set `s`, `ε ≤ √γ / 4` and the
quadratic average of `a` dominates `γ`, then the quadratic average of `b` dominates `γ / 2`.

The proof is the elementary inequality `b² ≥ a² - 2εa` (valid because `b ≥ max 0 (a - ε)`),
summed over `s`, together with Cauchy–Schwarz `(∑ a)² ≤ #s · ∑ a²`.  The hypothesis
`4ε ≤ √γ` upgrades to `16 #s ε² ≤ ∑ a²`, which is exactly what is needed to absorb the
`2ε ∑ a` term. -/
theorem avg_sq_perturb {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    {a b : ι → ℝ} {ε γ : ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hpert : ∀ i ∈ s, a i - ε ≤ b i)
    (hsmall : 4 * ε ≤ Real.sqrt γ)
    (hagg : γ ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, (a i) ^ 2) :
    γ / 2 ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, (b i) ^ 2 := by
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hn : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcard
  set A : ℝ := ∑ i ∈ s, (a i) ^ 2 with hA
  set B : ℝ := ∑ i ∈ s, (b i) ^ 2 with hB
  set Sa : ℝ := ∑ i ∈ s, a i with hSa
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg fun i hi => ha i hi
  -- pointwise: `bᵢ² ≥ aᵢ² - 2εaᵢ`
  have hpt : ∀ i ∈ s, (a i) ^ 2 - 2 * ε * a i ≤ (b i) ^ 2 := by
    intro i hi
    have hai := ha i hi
    have hbi := hb i hi
    have hpi := hpert i hi
    rcases le_or_gt 0 (a i - ε) with h | h
    · have h2 : (a i - ε) ^ 2 ≤ (b i) ^ 2 := pow_le_pow_left₀ h hpi 2
      nlinarith [h2, sq_nonneg ε]
    · nlinarith [mul_nonneg hai (by linarith : (0 : ℝ) ≤ 2 * ε - a i), sq_nonneg (b i)]
  have hsum : A - 2 * ε * Sa ≤ B := by
    have h3 : 2 * ε * Sa = ∑ i ∈ s, 2 * ε * a i := by
      rw [hSa, Finset.mul_sum]
    rw [hA, hB, h3, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hpt
  have hCS : Sa ^ 2 ≤ (s.card : ℝ) * A := by
    rw [hSa, hA]; exact sq_sum_le_card_mul_sum_sq
  have hsq_eps : 16 * ε ^ 2 ≤ γ := by
    have h1 : (4 * ε) ^ 2 ≤ (Real.sqrt γ) ^ 2 := pow_le_pow_left₀ (by linarith) hsmall 2
    rw [Real.sq_sqrt (le_of_lt hγ)] at h1
    nlinarith [h1]
  have h16 : 16 * (s.card : ℝ) * ε ^ 2 ≤ A := by
    have h2 : (s.card : ℝ) * γ ≤ A := by
      have h := mul_le_mul_of_nonneg_left hagg (le_of_lt hn)
      rwa [mul_inv_cancel_left₀ (ne_of_gt hn) A] at h
    have h3 : (s.card : ℝ) * (16 * ε ^ 2) ≤ (s.card : ℝ) * γ :=
      mul_le_mul_of_nonneg_left hsq_eps (le_of_lt hn)
    nlinarith [h2, h3]
  have h2e : 2 * ε * Sa ≤ A / 2 := by
    have hsq : (2 * ε * Sa) ^ 2 ≤ (A / 2) ^ 2 := by
      have h4 : 4 * ε ^ 2 * Sa ^ 2 ≤ 4 * ε ^ 2 * ((s.card : ℝ) * A) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
      have h5 : 4 * ((s.card : ℝ)) * ε ^ 2 ≤ A / 4 := by linarith [h16]
      have h6 : 4 * ((s.card : ℝ)) * ε ^ 2 * A ≤ A / 4 * A :=
        mul_le_mul_of_nonneg_right h5 hA0
      nlinarith [h4, h6]
    have hnn1 : 0 ≤ 2 * ε * Sa := by positivity
    have hnn2 : 0 ≤ A / 2 := by positivity
    have h3 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at h3
  have hB : A / 2 ≤ B := by linarith [hsum, h2e]
  have hfin : γ / 2 ≤ ((s.card : ℝ))⁻¹ * (A / 2) := by linarith [hagg]
  have hfin2 : ((s.card : ℝ))⁻¹ * (A / 2) ≤ ((s.card : ℝ))⁻¹ * B :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  linarith [hfin, hfin2]

end Work.Peluse.Ulower.StepLe
