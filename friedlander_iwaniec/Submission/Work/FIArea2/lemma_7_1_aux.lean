/-
# Auxiliary vocabulary for Lemma 7.1 of Friedlander–Iwaniec

This module collects the elementary geometric facts about the biquadratic form
`g(t₁,t₂) = t₁⁴ − 2γt₁²t₂² + t₂⁴` of *FI* (7.1) that the proof of Lemma 7.1 (the Fourier
integral bound (7.5)) uses: the non-strict version of the ellipse bounds (7.3) on the *closed*
region `M/4 ≤ g ≤ 4M`, and the elementary consequences of the support hypothesis
`f u ≠ 0 → M/4 ≤ u ≤ 4M`.
-/
import Mathlib
import Submission.Work.FIArea2.biquadratic_ellipse_bounds

set_option autoImplicit false

namespace Work.FIArea2

noncomputable section

open scoped BigOperators

/-- The biquadratic form `g(t₁,t₂) = t₁⁴ − 2γt₁²t₂² + t₂⁴` of *FI* (7.1), whose level sets are
considered in (7.2)–(7.4). -/
def gq (γ t₁ t₂ : ℝ) : ℝ := t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4

lemma gq_symm (γ t₁ t₂ : ℝ) : gq γ t₁ t₂ = gq γ t₂ t₁ := by
  simp only [gq]; ring

lemma one_sub_gamma_sq_pos (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : 0 < 1 - γ ^ 2 := by
  nlinarith [hγ0, hγ1, mul_pos (sub_pos.mpr hγ1) (by linarith : (0:ℝ) < 1 + γ)]

/-- **(7.3)–(7.4) on the closed region.**  For `0 ≤ γ < 1`, `M > 0` and a point of the region
`M/4 ≤ g(t₁,t₂) ≤ 4M`, the two "square annulus" bounds hold: the level region is squeezed between
`|t₁² − t₂²| ≤ 2√M` and `√M/2 ≤ t₁² + t₂² ≤ 4√M/√(1−γ²)`.  This is the non-strict form of
`biquadratic_ellipse_bounds`, which is what the pointwise derivative bounds of Lemma 7.1 use. -/
theorem region_bounds (M γ t₁ t₂ : ℝ) (hM : 0 < M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hlo : M / 4 ≤ gq γ t₁ t₂) (hhi : gq γ t₁ t₂ ≤ 4 * M) :
    |t₁ ^ 2 - t₂ ^ 2| ≤ 2 * Real.sqrt M ∧ Real.sqrt M / 2 ≤ t₁ ^ 2 + t₂ ^ 2 ∧
      t₁ ^ 2 + t₂ ^ 2 ≤ 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2) := by
  obtain ⟨⟨hc1, hc2, hc3⟩, -⟩ := biquadratic_ellipse_bounds γ M t₁ t₂ hγ0 hγ1 hM
  simp only [gq] at hlo hhi
  have hpos : 0 < 1 - γ ^ 2 := one_sub_gamma_sq_pos γ hγ0 hγ1
  have hsq_pos : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr hpos
  have hsqrtM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  refine ⟨?_, ?_, ?_⟩
  · have h4 : (t₁ ^ 2 - t₂ ^ 2) ^ 2 ≤ (2 * Real.sqrt M) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hM.le]; linarith
    have := sq_le_sq.mp h4
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt M)] at this
  · have h4 : (Real.sqrt M / 2) ^ 2 ≤ (t₁ ^ 2 + t₂ ^ 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hM.le]; linarith [hc3, hlo]
    have h1 := sq_le_sq.mp h4
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt M / 2), abs_of_nonneg (by positivity)] at h1
    exact h1
  · have hAB : (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ 2 * (t₁ ^ 4 + t₂ ^ 4) := by
      nlinarith [sq_nonneg (t₁ ^ 2 - t₂ ^ 2)]
    have h1 : (1 - γ ^ 2) * (t₁ ^ 4 + t₂ ^ 4) ≤ 8 * M := by linarith
    have h2 : ((t₁ ^ 2 + t₂ ^ 2) * Real.sqrt (1 - γ ^ 2)) ^ 2 ≤ (4 * Real.sqrt M) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpos.le, mul_pow, Real.sq_sqrt hM.le]
      nlinarith [hAB, h1, hpos.le]
    have h3 := sq_le_sq.mp h2
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.sqrt M)]
      at h3
    rw [le_div_iff₀ hsq_pos]
    linarith

/-- Support fact: `f` vanishes strictly below `M/4`. -/
lemma f_eq_zero_of_lt (M : ℝ) (f : ℝ → ℝ)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) {u : ℝ} (hu : u < M / 4) : f u = 0 := by
  by_contra h
  exact absurd (hfsupp u h).1 (not_le.mpr hu)

/-- Support fact: `f` vanishes strictly above `4M`. -/
lemma f_eq_zero_of_gt (M : ℝ) (f : ℝ → ℝ)
    (hfsupp : ∀ u, f u ≠ 0 → M / 4 ≤ u ∧ u ≤ 4 * M) {u : ℝ} (hu : 4 * M < u) : f u = 0 := by
  by_contra h
  exact absurd (hfsupp u h).2 (not_le.mpr hu)

/-- `|f| ≤ 1`, from the `j = 0` case of the derivative bound. -/
lemma abs_f_le_one (M : ℝ) (f : ℝ → ℝ)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j f u| ≤ M ^ (-(j : ℝ))) (u : ℝ) :
    |f u| ≤ 1 := by
  have := hfd 0 (by norm_num) u
  simpa using this

end

end Work.FIArea2
