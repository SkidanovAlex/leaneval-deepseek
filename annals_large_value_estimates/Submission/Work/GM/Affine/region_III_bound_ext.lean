import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_III_bound

/-!
# GM §9, region III of the fine case, extended

`region_III_bound` (GM Lemma 9.2, region III) bounds the `L²` mass of the smoothed majorant
`ghat K M₁ M₂ M₃ f` outside `[-T⁶, T⁶]` provided `M₃ ≤ Mbig`.  Here we extend the admissible
range of `M₃` to `M₃ ≤ C₃ · Mbig` for an arbitrary constant `C₃ ≥ 1`: the only place where the
hypothesis `M₃ ≤ Mbig` was used is the cardinality estimate for the `m₃`-range, and the constant
in the conclusion is allowed to depend on `C₃`.

The proof is that of `region_III_bound` with the cardinality bound
`card_prod_le_of_R2_ne_ext` replacing `card_prod_le_of_R2_ne`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ### Cardinality bound with `M₃ ≤ C₃ Mbig` -/

/-- The number of terms of the triple sum is bounded by `80 (2|K|+8) C₃ Mbig³` under the weaker
hypothesis `M₃ ≤ C₃ Mbig` (with `C₃ ≥ 1`). -/
lemma card_prod_le_of_R2_ne_ext {K C₃ M₁ M₂ M₃ Mbig : ℝ} (hC₃ : 1 ≤ C₃) (hK : 0 < K)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) (hM₁M : M₁ ≤ Mbig) (hM₂M : M₂ ≤ Mbig)
    (hM₃M : M₃ ≤ C₃ * Mbig) (hcard : (R2 M₂).card ≠ 0) :
    ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
      ≤ 80 * (2 * |K| + 8) * C₃ * Mbig ^ 3 := by
  have hMbigpos : 0 < Mbig := lt_of_lt_of_le hM₂ hM₂M
  have hC₃nn : (0 : ℝ) ≤ C₃ := le_trans zero_le_one hC₃
  have hhalf : (1 / 2 : ℝ) ≤ Mbig := by
    have h1 : (1 : ℝ) ≤ ((R2 M₂).card : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcard)
    have h2 : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := card_R2_le M₂ hM₂
    linarith
  have hCM : (1 / 2 : ℝ) ≤ C₃ * Mbig := by
    have h1 : (1 : ℝ) * (1 / 2) ≤ C₃ * Mbig :=
      mul_le_mul hC₃ hhalf (by norm_num) hC₃nn
    linarith
  have hc1 : ((R1 M₁).card : ℝ) ≤ 4 * M₁ + 1 := card_R1_le M₁ hM₁
  have hc2 : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := card_R2_le M₂ hM₂
  have hc3 : ((R3ext K M₃).card : ℝ) ≤ 2 * (K + 1) * M₃ + 3 := card_R3ext_le_general hK hM₃
  have hc1' : (0 : ℝ) ≤ ((R1 M₁).card : ℝ) := by positivity
  have hc2' : (0 : ℝ) ≤ ((R2 M₂).card : ℝ) := by positivity
  have hc3' : (0 : ℝ) ≤ ((R3ext K M₃).card : ℝ) := by positivity
  have hprod : ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
      ≤ (4 * M₁ + 1) * (2 * M₂) * (2 * (K + 1) * M₃ + 3) := by
    apply mul_le_mul
    · exact mul_le_mul hc1 hc2 hc2' (by positivity)
    · exact hc3
    · exact hc3'
    · positivity
  -- a uniform bound on the `m₃`-cardinality (both regimes use `C₃ Mbig ≥ 1/2`)
  have hb : 2 * (K + 1) * M₃ + 3 ≤ (2 * |K| + 8) * C₃ * Mbig := by
    have hK1 : (0 : ℝ) ≤ 2 * (K + 1) := by linarith
    have e1 : 2 * (K + 1) * M₃ ≤ 2 * (K + 1) * (C₃ * Mbig) :=
      mul_le_mul_of_nonneg_left hM₃M hK1
    have e2 : 3 ≤ 6 * (C₃ * Mbig) := by linarith [hCM]
    have hKabs : K ≤ |K| := le_abs_self K
    nlinarith [e1, e2, hKabs, hC₃nn, hMbigpos]
  by_cases hbig : (1 : ℝ) ≤ Mbig
  · have hA : 4 * M₁ + 1 ≤ 5 * Mbig := by linarith
    have hB : 2 * M₂ ≤ 2 * Mbig := by linarith
    have hD : (0 : ℝ) ≤ (2 * |K| + 8) * C₃ * Mbig ^ 3 := by positivity
    calc ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
        ≤ (4 * M₁ + 1) * (2 * M₂) * (2 * (K + 1) * M₃ + 3) := hprod
      _ ≤ (5 * Mbig) * (2 * Mbig) * ((2 * |K| + 8) * C₃ * Mbig) := by
          apply mul_le_mul
          · exact mul_le_mul hA hB (by positivity) (by positivity)
          · exact hb
          · positivity
          · positivity
      _ = 10 * (2 * |K| + 8) * C₃ * Mbig ^ 3 := by ring
      _ ≤ 80 * (2 * |K| + 8) * C₃ * Mbig ^ 3 := by nlinarith [hD]
  · push Not at hbig
    have hM₁1 : M₁ < 1 := lt_of_le_of_lt hM₁M hbig
    have hM₂1 : M₂ < 1 := lt_of_le_of_lt hM₂M hbig
    have hA : 4 * M₁ + 1 ≤ 5 := by linarith
    have hB : 2 * M₂ ≤ 2 := by linarith
    have hMbig2 : (1 : ℝ) ≤ 8 * Mbig ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 2
      norm_num at h
      linarith
    have hD : (0 : ℝ) ≤ (2 * |K| + 8) * C₃ * Mbig := by positivity
    calc ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
        ≤ (4 * M₁ + 1) * (2 * M₂) * (2 * (K + 1) * M₃ + 3) := hprod
      _ ≤ 5 * 2 * ((2 * |K| + 8) * C₃ * Mbig) := by
          apply mul_le_mul
          · exact mul_le_mul hA hB (by positivity) (by norm_num)
          · exact hb
          · positivity
          · norm_num
      _ = 10 * (2 * |K| + 8) * C₃ * Mbig := by ring
      _ ≤ 80 * (2 * |K| + 8) * C₃ * Mbig ^ 3 := by
          have h8 : 10 * (2 * |K| + 8) * C₃ * Mbig ≤ 10 * (2 * |K| + 8) * C₃ * Mbig * (8 * Mbig ^ 2) :=
            le_mul_of_one_le_right (by positivity) hMbig2
          have h50 : 10 * (2 * |K| + 8) * C₃ * Mbig * (8 * Mbig ^ 2)
              = 80 * (2 * |K| + 8) * C₃ * Mbig ^ 3 := by ring
          linarith [h8, h50.symm.le, h50.le]

/-! ### Region III, extended -/

/-- **Region III of GM Lemma 9.2, extended range.** For `|ξ| > T^6` and `M₃ ≤ C₃ Mbig`
(`C₃ ≥ 1`) the Fourier decay hypothesis (with the budget `Λ ≤ 16 c 2 1 T³ ∫f` and
`Mbig ≤ T^4`) makes `ghat` negligible:
`∫_{|ξ|>T^6} ‖ghat‖² ≤ C' T^δ Mbig^6 (∫f)²`, with `C'` allowed to depend on `C₃`. -/
theorem region_III_bound_ext {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ C₃ * Mbig → Mbig ≤ T ^ 4 →
        (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          ≤ C' * T ^ δ * Mbig ^ 6 * (∫ u, f u) ^ 2 := by
  refine ⟨204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdecay hΛbd Mbig M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hMbigT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < T₀) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hSupp
  set A : ℝ := ∫ u, f u with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact integral_nonneg hfnn
  have hc21 : 0 < c 2 1 := by
    have h1 : 0 < 16 * c 2 1 * T ^ 3 * A := by
      rw [hAdef] at hΛbd
      exact lt_of_lt_of_le hΛ hΛbd
    have h2 : 0 ≤ 16 * T ^ 3 * A := by positivity
    have h3 : 0 < c 2 1 * (16 * T ^ 3 * A) := by
      rw [show c 2 1 * (16 * T ^ 3 * A) = 16 * c 2 1 * T ^ 3 * A by ring]
      exact h1
    exact pos_of_mul_pos_left h3 h2
  set B : ℝ := c 2 1 * T ^ 3 * Λ with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hFhatA : ∀ η : ℝ, ‖Fhat f η‖ ≤ A := by
    intro η
    rw [hAdef]
    exact norm_Fhat_le_integral hfnn η
  have hFhatB : ∀ η : ℝ, η ≠ 0 → ‖Fhat f η‖ ≤ B / η ^ 2 := by
    intro η hη
    have h1 := hdecay 2 1 (by norm_num) η hη
    rw [hBdef]
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_one, div_pow, sq_abs]
    field_simp
    try ring
  have hT6 : (0 : ℝ) < T ^ 6 := by positivity
  set N : ℝ := ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hpt : ∀ ξ : ℝ, ξ ≠ 0 → ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ N ^ 2 * A * B / ξ ^ 2 := by
    intro ξ hξ
    rw [hNdef]
    exact ghat_sq_le hK hM₁ hM₂ hM₃ hf hcs hA0 hB0 hFhatA hFhatB hξ
  have hint1 : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ N ^ 2 * A * B / T ^ 6 := by
    have hle : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ ∫ ξ in Set.Ioi (T ^ 6), (N ^ 2 * A * B) / ξ ^ 2 := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun ξ => by positivity)
      · exact (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).1
      · show ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Ioi (T ^ 6))),
            ‖ghat K M₁ M₂ M₃ f a‖ ^ 2 ≤ (N ^ 2 * A * B) / a ^ 2
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        filter_upwards with ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro h0
          rw [h0] at hξ
          simp only [Set.mem_Ioi] at hξ
          linarith [hT6]
        exact hpt ξ hξ0
    exact hle.trans (le_of_eq (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).2.1)
  have hint2 : (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ N ^ 2 * A * B / T ^ 6 := by
    have hle : (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ ∫ ξ in Set.Iio (-(T ^ 6)), (N ^ 2 * A * B) / ξ ^ 2 := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun ξ => by positivity)
      · exact (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).2.2.1
      · show ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Iio (-(T ^ 6)))),
            ‖ghat K M₁ M₂ M₃ f a‖ ^ 2 ≤ (N ^ 2 * A * B) / a ^ 2
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iio]
        filter_upwards with ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro h0
          rw [h0] at hξ
          simp only [Set.mem_Iio] at hξ
          linarith [hT6]
        exact hpt ξ hξ0
    exact hle.trans (le_of_eq (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).2.2.2)
  have hsum_int : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ 2 * N ^ 2 * A * B / T ^ 6 := by
    have h2 : (2 : ℝ) * (N ^ 2 * A * B / T ^ 6) = 2 * N ^ 2 * A * B / T ^ 6 := by ring
    rw [← h2]
    linarith [hint1, hint2]
  have hAB : A * B ≤ 16 * (c 2 1) ^ 2 * T ^ 6 * A ^ 2 := by
    have h1 : Λ ≤ 16 * c 2 1 * T ^ 3 * A := by rw [hAdef] at hΛbd; exact hΛbd
    rw [hBdef]
    calc A * (c 2 1 * T ^ 3 * Λ)
        ≤ A * (c 2 1 * T ^ 3 * (16 * c 2 1 * T ^ 3 * A)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 * (c 2 1) ^ 2 * T ^ 6 * A ^ 2 := by ring
  have hmain : 2 * N ^ 2 * A * B / T ^ 6 ≤ 32 * (c 2 1) ^ 2 * N ^ 2 * A ^ 2 := by
    rw [div_le_iff₀ hT6]
    have h2 : (0 : ℝ) ≤ 2 * N ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hAB h2
    nlinarith [h3, hT6]
  by_cases hcard : (R2 M₂).card = 0
  · have hzero : ∀ ξ : ℝ, ghat K M₁ M₂ M₃ f ξ = 0 := by
      intro ξ
      rw [ghat_fourier_expansion hK hM₁ hM₂ hM₃ hf hcs ξ, Finset.card_eq_zero.mp hcard]
      simp
    have hz1 : (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext ξ
      rw [hzero ξ]
      simp
    rw [hz1]
    simp only [MeasureTheory.integral_zero, add_zero]
    have hTd : 0 < T ^ δ := Real.rpow_pos_of_pos hT0 δ
    have hCpos : (0 : ℝ) < 204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1 := by
      positivity
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hMbig6 : (0 : ℝ) ≤ Mbig ^ 6 := by positivity
    have hfin : 0 ≤ (204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1) * T ^ δ
        * Mbig ^ 6 * A ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCpos) (le_of_lt hTd)) hMbig6) hA2
    linarith
  · have hNle := card_prod_le_of_R2_ne_ext hC₃ hK hM₁ hM₂ hM₃ hM₁M hM₂M hM₃M hcard
    have hNle' : N ≤ 80 * (2 * |K| + 8) * C₃ * Mbig ^ 3 := by rw [hNdef]; exact hNle
    have hN2 : N ^ 2 ≤ 6400 * (2 * |K| + 8) ^ 2 * C₃ ^ 2 * Mbig ^ 6 := by
      calc N ^ 2 ≤ (80 * (2 * |K| + 8) * C₃ * Mbig ^ 3) ^ 2 := pow_le_pow_left₀ hN0 hNle' 2
        _ = 6400 * (2 * |K| + 8) ^ 2 * C₃ ^ 2 * Mbig ^ 6 := by ring
    have hXY : 204800 * (c 2 1) ^ 2 * (2 * |K| + 8) ^ 2 * C₃ ^ 2
        ≤ (204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1) * T ^ δ := by
      have h1 : 204800 * (c 2 1) ^ 2 * (2 * |K| + 8) ^ 2 * C₃ ^ 2
          ≤ 204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1 := by
        nlinarith [mul_nonneg (sq_nonneg (2 * |K| + 8)) (sq_nonneg C₃),
          sq_nonneg (c 2 1), sq_nonneg (2 * |K| + 8), sq_nonneg C₃]
      have h2 : (0 : ℝ) ≤ 204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1 := by
        positivity
      exact h1.trans (le_mul_of_one_le_right h2 (Real.one_le_rpow hT1 (le_of_lt hδ)))
    have hMbig6 : (0 : ℝ) ≤ Mbig ^ 6 := by positivity
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    calc (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ 2 * N ^ 2 * A * B / T ^ 6 := hsum_int
      _ ≤ 32 * (c 2 1) ^ 2 * N ^ 2 * A ^ 2 := hmain
      _ ≤ 32 * (c 2 1) ^ 2 * (6400 * (2 * |K| + 8) ^ 2 * C₃ ^ 2 * Mbig ^ 6) * A ^ 2 := by
          have hc2 : (0 : ℝ) ≤ 32 * (c 2 1) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2 hc2) hA2
      _ = 204800 * (c 2 1) ^ 2 * (2 * |K| + 8) ^ 2 * C₃ ^ 2 * Mbig ^ 6 * A ^ 2 := by ring
      _ ≤ (204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 8) ^ 2 * C₃ ^ 2 + 1) * T ^ δ
            * Mbig ^ 6 * A ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXY hMbig6) hA2

end

end Work.GM.Affine
