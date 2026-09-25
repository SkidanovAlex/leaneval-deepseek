/-
The analytic core: the "bad interval" is impossible.

Using the L-series lower bound `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`
for the residue class `1 mod 3` (totient `2`), together with the dyadic bound
`primePart_tsum_le` on the prime part of the series and `nonprimePart_tsum_le` on its
prime-power part, we show that there cannot be an interval `[M, M ^ 400]` on which
`goodPrimeSum` stays below `(log 2 / 64) * N`.
-/
import Mathlib
import Submission.Work.Tower.APDensity.Basic
import Submission.Work.Tower.APDensity.Analytic.primePart_tsum_le
import Submission.Work.Tower.APDensity.Analytic.lambdaOne_tsum_split
import Submission.Work.Tower.APDensity.Analytic.nonprimePart_tsum_le

open scoped BigOperators
open Finset

namespace Work.Tower

lemma totient_three_inv : ((3 : ℕ).totient : ℝ)⁻¹ = 1 / 2 := by
  have h : Nat.totient 3 = 2 := by decide
  rw [h]
  norm_num

/-- The prime-power part of the Dirichlet series of `LambdaOne`, at exponent `1`. -/
noncomputable def nonprimeSeries : ℝ :=
  ∑' n : ℕ, (if n.Prime then 0 else LambdaOne n) / (n : ℝ)

lemma nonprimeSeries_nonneg : 0 ≤ nonprimeSeries := by
  rw [nonprimeSeries]
  refine tsum_nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h1 : 0 ≤ (if n.Prime then 0 else LambdaOne n) := by
      split_ifs with h
      · exact le_rfl
      · exact lambdaOne_nonneg n
    exact div_nonneg h1 (by positivity)

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  ring

lemma log_sixteen_eq : Real.log 16 = 2 * Real.log 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
  ring

lemma one_lt_log_four : 1 < Real.log 4 := by
  rw [log_four_eq]
  linarith [Real.log_two_gt_d9]

lemma exp_neg_twenty_le : Real.exp (-(20 : ℝ)) ≤ ((2 : ℝ) ^ 20)⁻¹ := by
  have hexp20 : (2 : ℝ) ^ 20 ≤ Real.exp 20 := by
    rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num)
      (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1) 20
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos 20) (by positivity)).mpr hexp20

/-- For every `M` large enough, there is `N ∈ [M, M ^ 400]` with
`(log 2 / 64) * N ≤ goodPrimeSum N`. -/
theorem bad_interval_impossible :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∃ N : ℕ,
      M ≤ (N : ℝ) ∧ (N : ℝ) ≤ M ^ (400 : ℝ) ∧ (Real.log 2 / 64) * (N : ℝ) ≤ goodPrimeSum N := by
  obtain ⟨C, hC⟩ := ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound
    (q := 3) (a := (1 : ZMod 3)) isUnit_one
  refine ⟨max 16 (Real.exp (0.3 * (C + nonprimeSeries + 2 * Real.log 4))),
    lt_max_of_lt_left (by norm_num), ?_⟩
  intro M hM
  have hM16 : 16 ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  by_contra hcon
  have hbad : ∀ N : ℕ, M ≤ (N : ℝ) → (N : ℝ) ≤ M ^ (400 : ℝ) →
      goodPrimeSum N ≤ (Real.log 2 / 64) * (N : ℝ) := by
    intro N h1 h2
    by_contra hlt
    exact hcon ⟨N, h1, h2, le_of_lt (not_le.mp hlt)⟩
  -- the exponent
  set δ : ℝ := 1 / (20 * Real.log M) with hδdef
  have hlogMpos : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogM16 : 2 * Real.log 4 ≤ Real.log M := by
    have h1 : Real.log 16 ≤ Real.log M := Real.log_le_log (by norm_num) hM16
    rw [log_sixteen_eq] at h1
    exact h1
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle1 : δ ≤ 1 := by
    have h3 : 0 < 20 * Real.log M := by linarith
    rw [hδdef, div_le_one h3]
    linarith [hlogM16, one_lt_log_four]
  have hδlog2 : δ * Real.log 2 ≤ 1 := by
    have h2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [hδle1, hδpos, h2]
  have hδlogM : δ * Real.log M = 1 / 20 := by
    have hne : (20 * Real.log M) ≠ 0 := ne_of_gt (by linarith)
    rw [hδdef, div_mul_eq_mul_div, one_mul,
      div_eq_div_iff hne (by norm_num : (20 : ℝ) ≠ 0)]
    ring
  have hδ400 : δ * 400 * Real.log M = 20 := by
    have : δ * 400 * Real.log M = 400 * (δ * Real.log M) := by ring
    rw [this, hδlogM]; norm_num
  -- the lower bound for the full series, at `x = 1 + δ`
  have hF := hC (x := 1 + δ) ⟨by linarith, by linarith⟩
  rw [show (1 + δ) - 1 = δ by ring, totient_three_inv] at hF
  -- the upper bounds for the two parts
  have hsplit := Work.Tower.APDensity.Analytic.lambdaOne_tsum_split hδpos
  have hP := Work.Tower.APDensity.Analytic.primePart_tsum_le (A := 400) (ε := Real.log 2 / 64) (δ := δ) (M := M)
    (by norm_num) hM1 (by positivity) hδpos hδle1 hbad
  have hNP := Work.Tower.APDensity.Analytic.nonprimePart_tsum_le (δ := δ) hδpos.le
  -- combine into a `δ`-scaled inequality
  have hmain : 1 / 2 - C * δ ≤
      δ * (2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)
        + 2 * (Real.log 2 / 64) / (1 - (2 : ℝ) ^ (-δ))
        + 4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)))
      + δ * nonprimeSeries := by
    have h1 : 1 / 2 - C * δ ≤ δ * (∑' n : ℕ, LambdaOne n / (n : ℝ) ^ (1 + δ)) := by
      have h2 := mul_le_mul_of_nonneg_left hF hδpos.le
      have h3 : δ * (1 / 2 / δ - C) = 1 / 2 - C * δ := by
        field_simp
        try ring
      linarith [h2, h3.le, h3.ge]
    have h3 : δ * (∑' n : ℕ, LambdaOne n / (n : ℝ) ^ (1 + δ))
        ≤ δ * ((2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)
            + 2 * (Real.log 2 / 64) / (1 - (2 : ℝ) ^ (-δ))
            + 4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)))
          + nonprimeSeries) := by
      refine mul_le_mul_of_nonneg_left ?_ hδpos.le
      rw [hsplit]
      exact add_le_add hP hNP
    calc 1 / 2 - C * δ ≤ δ * (∑' n : ℕ, LambdaOne n / (n : ℝ) ^ (1 + δ)) := h1
      _ ≤ δ * ((2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)
            + 2 * (Real.log 2 / 64) / (1 - (2 : ℝ) ^ (-δ))
            + 4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)))
          + nonprimeSeries) := h3
      _ = δ * (2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)
            + 2 * (Real.log 2 / 64) / (1 - (2 : ℝ) ^ (-δ))
            + 4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / (1 - (2 : ℝ) ^ (-δ)))
          + δ * nonprimeSeries := by ring
  -- term-by-term estimates
  have hterm1 : δ * (2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)) ≤ 1 / 5 + 1 / 20 := by
    have hL := log_two_floor_le_log_div hM1
    have h1 : 2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1)
        ≤ 2 * Real.log 4 * (Real.log M / Real.log 2 + 1) := by
      refine mul_le_mul_of_nonneg_left (by linarith [hL] : (Nat.log 2 ⌊M⌋₊ : ℝ) + 1
        ≤ Real.log M / Real.log 2 + 1) ?_
      have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
      linarith
    have hδ1 : δ * (2 * Real.log 4 * (Real.log M / Real.log 2 + 1))
        = 1 / 5 + 2 * Real.log 4 * δ := by
      have h : δ * (2 * Real.log 4 * (Real.log M / Real.log 2 + 1))
          = 2 * Real.log 4 * (δ * Real.log M) / Real.log 2 + 2 * Real.log 4 * δ := by ring
      rw [h, hδlogM, log_four_eq]
      have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      field_simp
      ring
    have h3 : 2 * Real.log 4 * δ ≤ 1 / 20 := by
      rw [hδdef, mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith [hlogM16]
    have h2 : δ * (2 * Real.log 4 * ((Nat.log 2 ⌊M⌋₊ : ℝ) + 1))
        ≤ δ * (2 * Real.log 4 * (Real.log M / Real.log 2 + 1)) :=
      mul_le_mul_of_nonneg_left h1 hδpos.le
    linarith [h2, hδ1.le, hδ1.ge, h3]
  have hterm2 : δ * (2 * (Real.log 2 / 64) / (1 - (2 : ℝ) ^ (-δ))) ≤ 1 / 16 := by
    have h := div_one_sub_two_rpow_neg_le_mul hδpos hδlog2
      (by positivity : (0 : ℝ) ≤ 2 * (Real.log 2 / 64))
    have h2 := mul_le_mul_of_nonneg_left h hδpos.le
    have h3 : δ * (2 * (2 * (Real.log 2 / 64)) / (δ * Real.log 2)) = 1 / 16 := by
      field_simp
      ring
    linarith [h2, h3.le, h3.ge]
  have hterm3 : δ * (4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M))
        / (1 - (2 : ℝ) ^ (-δ))) ≤ 16 / 2 ^ 20 := by
    have h4 : Real.exp (-(δ * 400 * Real.log M)) ≤ ((2 : ℝ) ^ 20)⁻¹ := by
      rw [hδ400]
      exact exp_neg_twenty_le
    have key : 4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / (1 - (2 : ℝ) ^ (-δ))
        ≤ 2 * (4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M))) / (δ * Real.log 2) :=
      div_one_sub_two_rpow_neg_le_mul hδpos hδlog2 (by positivity)
    have h := mul_le_mul_of_nonneg_left key hδpos.le
    have h3 : δ * (2 * (4 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M))) / (δ * Real.log 2))
        = 8 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / Real.log 2 := by
      field_simp
      ring
    have h5 : 8 * Real.log 4 * Real.exp (-(δ * 400 * Real.log M)) / Real.log 2 ≤ 16 / 2 ^ 20 := by
      rw [log_four_eq]
      have h16 : 8 * (2 * Real.log 2) * Real.exp (-(δ * 400 * Real.log M)) / Real.log 2
          = 16 * Real.exp (-(δ * 400 * Real.log M)) := by
        field_simp
        ring
      rw [h16]
      have h6 : 16 * Real.exp (-(δ * 400 * Real.log M)) ≤ 16 * ((2 : ℝ) ^ 20)⁻¹ :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
      simpa only [div_eq_mul_inv] using h6
    linarith [h, h3.le, h3.ge, h5]
  have hterm4 : (C + nonprimeSeries) * δ ≤ 1 / 6 := by
    have hexpK : Real.exp (0.3 * (C + nonprimeSeries + 2 * Real.log 4)) ≤ M :=
      le_trans (le_max_right _ _) hM
    have hlogK : 0.3 * (C + nonprimeSeries + 2 * Real.log 4) ≤ Real.log M := by
      have := Real.log_le_log (Real.exp_pos _) hexpK
      rwa [Real.log_exp] at this
    have hK : (C + nonprimeSeries + 2 * Real.log 4) / (20 * Real.log M) ≤ 1 / 6 := by
      rw [div_le_iff₀ (by linarith [hlogMpos])]
      linarith
    have h2 : (C + nonprimeSeries) * δ ≤ (C + nonprimeSeries + 2 * Real.log 4) * δ := by
      have : 0 ≤ 2 * Real.log 4 * δ := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
        nlinarith [hδpos]
      nlinarith
    have h3 : (C + nonprimeSeries + 2 * Real.log 4) * δ
        = (C + nonprimeSeries + 2 * Real.log 4) / (20 * Real.log M) := by
      rw [hδdef, mul_one_div]
    linarith [h2, h3.le, h3.ge, hK]
  -- final contradiction
  have hsum : (1 : ℝ) / 2 ≤ 1 / 5 + 1 / 20 + 1 / 16 + 16 / 2 ^ 20 + 1 / 6 := by
    linarith [hmain, hterm1, hterm2, hterm3, hterm4]
  norm_num at hsum

end Work.Tower
