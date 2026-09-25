import Mathlib
import Submission.Commons.Analysis.Fourier.maximal_dilation_convolution_l2

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.Fourier

open Commons.Analysis.Maximal (hlMax)

/-- The `enorm` of a complex number is the `ofReal` of its norm. -/
lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- A purely imaginary exponential has unit modulus, in the shape needed for modulations
`e^{-I·a·x}`. -/
lemma enorm_exp_neg_I_mul (a x : ℝ) :
    ‖Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ)))‖ₑ = 1 := by
  have harg : -(Complex.I * (a : ℂ) * (x : ℂ)) = (((-(a * x)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.enorm_exp_ofReal_mul_I]

/-- Cauchy–Schwarz in `ℝ≥0∞`, stated for sums of `ofReal`s: the square of the sum of `K` terms
is bounded by `K` times the sum of the squares. -/
lemma ofReal_sum_sq_le_card_mul_sum_sq {K : ℕ} (b : Fin K → ℝ) (hb : ∀ k, 0 ≤ b k) :
    (∑ k, ENNReal.ofReal (b k)) ^ (2 : ℝ) ≤
      (K : ℝ≥0∞) * ∑ k, (ENNReal.ofReal (b k)) ^ (2 : ℝ) := by
  have hCS : (∑ k, b k) ^ 2 ≤ (K : ℝ) * ∑ k, (b k) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
  have hR : (K : ℝ≥0∞) * ∑ k, (ENNReal.ofReal (b k)) ^ (2 : ℝ)
      = ENNReal.ofReal ((K : ℝ) * ∑ k, (b k) ^ 2) := by
    have hpow : ∀ k, (ENNReal.ofReal (b k)) ^ (2 : ℝ) = ENNReal.ofReal ((b k) ^ 2) := by
      intro k
      rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hb k)]
    simp only [hpow]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg (b k)),
      ← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (by positivity)]
  rw [hR, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hb k), ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (Finset.sum_nonneg fun k _ => hb k) 2]
  exact ENNReal.ofReal_le_ofReal hCS

/-- **Chebyshev / Cauchy–Schwarz in `ℝ≥0∞`**: the square of a sum of `K` terms is at most `K`
times the sum of the squares.  (The `ℝ≥0∞` analogue of `sq_sum_le_card_mul_sum_sq`; the cases with
a `⊤` summand are immediate since both sides are then `⊤`.) -/
lemma sum_sq_le_card_mul_sum_sq (K : ℕ) (a : Fin K → ℝ≥0∞) :
    (∑ k, a k) ^ 2 ≤ (K : ℝ≥0∞) * ∑ k, (a k) ^ 2 := by
  by_cases h : ∀ k, a k ≠ ⊤
  · have h1 : ∀ k, (ENNReal.ofReal (a k).toReal) ^ (2 : ℝ) = (a k) ^ 2 := by
      intro k
      rw [ENNReal.rpow_two, ENNReal.ofReal_toReal (h k), ← ENNReal.rpow_two]
    calc (∑ k, a k) ^ 2
        = (∑ k, ENNReal.ofReal ((a k).toReal)) ^ (2 : ℝ) := by
          rw [ENNReal.rpow_two]
          congr 1
          exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_toReal (h k)).symm
      _ ≤ (K : ℝ≥0∞) * ∑ k, (ENNReal.ofReal ((a k).toReal)) ^ (2 : ℝ) :=
          ofReal_sum_sq_le_card_mul_sum_sq (fun k => (a k).toReal)
            (fun _ => ENNReal.toReal_nonneg)
      _ = (K : ℝ≥0∞) * ∑ k, (a k) ^ 2 := by
          rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    have hsum : (∑ k, a k) = ⊤ := ENNReal.sum_eq_top.mpr ⟨k, Finset.mem_univ k, hk⟩
    have hsum2 : (∑ k, (a k) ^ 2) = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨k, Finset.mem_univ k, by rw [hk]; exact ENNReal.top_pow (by decide)⟩
    have hKpos : 0 < K := k.pos
    have hK : (K : ℝ≥0∞) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hKpos.ne'
    have h2 : (∑ k, a k) ^ 2 = (K : ℝ≥0∞) * ∑ k, (a k) ^ 2 := by
      rw [hsum, hsum2, ENNReal.top_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.mul_top hK]
    exact le_of_eq h2

/-- Cauchy–Schwarz in `ℝ≥0∞` for complex numbers: `(∑ ‖z k‖ₑ)² ≤ K * ∑ (‖z k‖ₑ)²`. -/
lemma sum_enorm_sq_le_card_mul_sum_enorm_sq {K : ℕ} (z : Fin K → ℂ) :
    (∑ k, ‖z k‖ₑ) ^ (2 : ℝ) ≤ (K : ℝ≥0∞) * ∑ k, (‖z k‖ₑ) ^ (2 : ℝ) := by
  simpa only [ENNReal.rpow_two] using sum_sq_le_card_mul_sum_sq K (fun k => ‖z k‖ₑ)


/-- `rpow` with exponent `2` commutes with arbitrary suprema in `ℝ≥0∞`. -/
lemma iSup_rpow_two {ι : Type*} (f : ι → ℝ≥0∞) :
    (⨆ i, f i) ^ (2 : ℝ) = ⨆ i, (f i) ^ (2 : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [← ENNReal.le_rpow_inv_iff (show (0 : ℝ) < 2 by norm_num)]
    refine iSup_le fun i => ?_
    rw [ENNReal.le_rpow_inv_iff (show (0 : ℝ) < 2 by norm_num)]
    exact le_iSup (fun i => (f i) ^ (2 : ℝ)) i
  · exact iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) (by norm_num)

/-- **Pointwise Hardy--Littlewood domination of the modulated maximal dilated convolution.**
For a Schwartz window `Ψ` and `g ∈ L²(ℝ)` the maximal dilated convolution is dominated, uniformly in
the scale `t > 0`, by a constant times the Hardy--Littlewood maximal function of `‖g‖ₑ`; a unit
modulus modulation `e^{-I·a·x}` does not change this. -/
theorem maximal_dilation_convolution_modulated_enorm_le_hlMax (Ψ : SchwartzMap ℝ ℂ) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ), MemLp g 2 (volume : Measure ℝ) → ∀ x : ℝ,
      (⨆ t : {t : ℝ // 0 < t},
        ‖Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ))) *
          (∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))))‖ₑ)
        ≤ ENNReal.ofReal C * hlMax (fun y : ℝ => ‖g y‖ₑ) x := by
  obtain ⟨Kr, hsym, hmono, _, hKmaj, hKtop, hKpos⟩ := exists_radial_decreasing_majorant Ψ
  refine ⟨(∫⁻ z, Kr z).toReal, ENNReal.toReal_pos hKpos.ne' hKtop, fun g hg x => ?_⟩
  refine iSup_le fun t => ?_
  have ht : (0 : ℝ) < (t : ℝ) := t.2
  have hgenorm : AEMeasurable (fun y : ℝ => ‖g y‖ₑ) volume := hg.aemeasurable.enorm
  rw [enorm_mul, enorm_exp_neg_I_mul a x, one_mul]
  calc ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ
      ≤ ∫⁻ y, ‖g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖g y‖ₑ * ‖(t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))‖ₑ :=
        lintegral_congr fun y => enorm_mul _ _
    _ ≤ ∫⁻ y, ‖g y‖ₑ * (ENNReal.ofReal (t : ℝ)⁻¹ * Kr ((x - y) / (t : ℝ))) := by
        refine lintegral_mono fun y => ?_
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        refine le_trans (enorm_smul_le (r := (t : ℝ)⁻¹)
          (x := Ψ ((x - y) / (t : ℝ)))) ?_
        rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr ht)]
        exact mul_le_mul_of_nonneg_left (hKmaj _) bot_le
    _ ≤ (∫⁻ z, Kr z) * hlMax (fun y : ℝ => ‖g y‖ₑ) x :=
        lintegral_convolution_dilate_ae_le_hlMax Kr hsym hmono _ hgenorm ht x
    _ = ENNReal.ofReal ((∫⁻ z, Kr z).toReal) * hlMax (fun y : ℝ => ‖g y‖ₑ) x := by
        rw [ENNReal.ofReal_toReal hKtop]

/-- Unmodulated case of `maximal_dilation_convolution_modulated_enorm_le_hlMax`. -/
theorem maximal_dilation_convolution_enorm_le_hlMax (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ), MemLp g 2 (volume : Measure ℝ) → ∀ x : ℝ,
      (⨆ t : {t : ℝ // 0 < t},
        ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ)
        ≤ ENNReal.ofReal C * hlMax (fun y : ℝ => ‖g y‖ₑ) x := by
  obtain ⟨C, hCpos, hC⟩ := maximal_dilation_convolution_modulated_enorm_le_hlMax Ψ 0
  exact ⟨C, hCpos, fun g hg x => by simpa using hC g hg x⟩

/-- **A priori bound for the band sum of translated dilates.**  For a Schwartz window `Ψ`,
frequencies `lam`, and `h k ∈ L²(ℝ)`, the maximal function over the scales `t > 0` of the modulated
band sum `Σ_k e^{-I·lam k·x}(h k ⋆ Ψ_t)(x)` is bounded on `L²(ℝ)` by `C·K·∫⁻ Σ_k ‖h k‖²`.
(The phase factors have modulus one and each term is controlled by
`Commons.Analysis.Fourier.maximal_dilation_convolution_l2`; Cauchy–Schwarz over the `K` terms
gives the factor `K`.) -/
theorem lintegral_iSup_band_sum_dilation_le (K : ℕ) (lam : Fin K → ℝ) (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (h k) 2 (volume : Measure ℝ)) →
      ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
          ‖∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
            (∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))))‖ₑ) ^ (2 : ℝ)
          ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal (C * (K : ℝ))
            * ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖h k x‖ ^ 2) ∂(volume : Measure ℝ) := by
  obtain ⟨Kr, hsym, hmono, _, hKmaj, hKtop, hKpos⟩ := exists_radial_decreasing_majorant Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  set d : ℝ := (∫⁻ z, Kr z).toReal with hddef
  have hdpos : 0 < d := ENNReal.toReal_pos hKpos.ne' hKtop
  have hKeq : ∫⁻ z, Kr z = ENNReal.ofReal d := (ENNReal.ofReal_toReal hKtop).symm
  refine ⟨d ^ 2 * C₀ ^ 2, by positivity, fun h hh => ?_⟩
  set A : ℝ≥0∞ := ∫⁻ z, Kr z with hAdef
  have hAeq : A = ENNReal.ofReal d := by rw [hAdef]; exact hKeq
  have hAne : A ≠ ⊤ := by rw [hAeq]; exact ENNReal.ofReal_ne_top
  -- The phase factors have unit modulus.
  have hphase : ∀ (k : Fin K) (x : ℝ),
      ‖Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ)))‖ₑ = 1 :=
    fun k x => enorm_exp_neg_I_mul (lam k) x
  -- Pointwise-in-`t` domination by the Hardy--Littlewood maximal function.
  have hterm : ∀ (k : Fin K) (x : ℝ) (t : {t : ℝ // 0 < t}),
      ‖∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ
        ≤ A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x := by
    intro k x t
    have ht : (0 : ℝ) < (t : ℝ) := t.2
    have hgenorm : AEMeasurable (fun y : ℝ => ‖h k y‖ₑ) volume := (hh k).aemeasurable.enorm
    calc ‖∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ
        ≤ ∫⁻ y, ‖h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖h k y‖ₑ * ‖(t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))‖ₑ :=
          lintegral_congr fun y => enorm_mul _ _
      _ ≤ ∫⁻ y, ‖h k y‖ₑ * (ENNReal.ofReal (t : ℝ)⁻¹ * Kr ((x - y) / (t : ℝ))) := by
          refine lintegral_mono fun y => ?_
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          refine le_trans (enorm_smul_le (r := (t : ℝ)⁻¹)
            (x := Ψ ((x - y) / (t : ℝ)))) ?_
          rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr ht)]
          exact mul_le_mul_of_nonneg_left (hKmaj _) bot_le
      _ ≤ (∫⁻ z, Kr z) * hlMax (fun y : ℝ => ‖h k y‖ₑ) x :=
          lintegral_convolution_dilate_ae_le_hlMax Kr hsym hmono _ hgenorm ht x
      _ = A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x := by rw [hAdef]
  -- Pointwise domination of the band sum by `K` times the sum of the squares.
  have hpoint : ∀ x : ℝ,
      (⨆ t : {t : ℝ // 0 < t},
          ‖∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
            (∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))))‖ₑ) ^ (2 : ℝ)
        ≤ (K : ℝ≥0∞) * ∑ k : Fin K, (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) := by
    intro x
    rw [iSup_rpow_two]
    refine iSup_le fun t => ?_
    set z : Fin K → ℂ :=
      fun k => ∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))) with hz
    have hsum : ‖∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * z k‖ₑ
        ≤ ∑ k : Fin K, ‖z k‖ₑ := by
      calc ‖∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * z k‖ₑ
          ≤ ∑ k : Fin K, ‖Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * z k‖ₑ :=
            enorm_sum_le _ _
        _ = ∑ k : Fin K, ‖z k‖ₑ := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [enorm_mul, hphase k x, one_mul]
    calc (‖∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * z k‖ₑ) ^ (2 : ℝ)
        ≤ (∑ k : Fin K, ‖z k‖ₑ) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hsum (by norm_num)
      _ ≤ (K : ℝ≥0∞) * ∑ k : Fin K, (‖z k‖ₑ) ^ (2 : ℝ) :=
          sum_enorm_sq_le_card_mul_sum_enorm_sq z
      _ ≤ (K : ℝ≥0∞) * ∑ k : Fin K, (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          refine Finset.sum_le_sum fun k _ => ENNReal.rpow_le_rpow ?_ (by norm_num)
          have hzk : ‖z k‖ₑ
              = ‖∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ := by rw [hz]
          rw [hzk]
          exact hterm k x t
  -- Measurability of the dominating function.
  have hmeasM : ∀ k : Fin K,
      Measurable (fun x : ℝ => (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ)) := by
    intro k
    have h1 : Measurable (fun x : ℝ => A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) :=
      (Commons.Analysis.Maximal.measurable_hlMax _).const_mul A
    simpa only [ENNReal.rpow_two] using h1.pow_const 2
  have hmeas2 : ∀ k : Fin K,
      AEMeasurable (fun x : ℝ => ‖h k x‖ₑ ^ (2 : ℝ)) volume := by
    intro k
    simpa only [ENNReal.rpow_two] using ((hh k).aemeasurable.enorm).pow_const 2
  -- The `L²` bound for a single term.
  have hkbound : ∀ k : Fin K,
      ∫⁻ x, (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (d ^ 2 * C₀ ^ 2) * ∫⁻ x, ‖h k x‖ₑ ^ (2 : ℝ) := by
    intro k
    have hmul : ∫⁻ x, (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ)
        = A ^ 2 * ∫⁻ x, (hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) := by
      have h1 : ∀ x : ℝ, (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ)
          = A ^ 2 * (hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) := by
        intro x
        rw [ENNReal.rpow_two, ENNReal.rpow_two, mul_pow]
      simp only [h1]
      exact lintegral_const_mul' (A ^ 2) _ (ENNReal.pow_ne_top hAne)
    have hHL : ∫⁻ x, (hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ‖h k x‖ₑ ^ (2 : ℝ) := by
      simpa only [enorm_norm_eq_enorm, hlMax, ENNReal.rpow_two, Real.rpow_two]
        using hC₀ (fun y : ℝ => ‖h k y‖)
    calc ∫⁻ x, (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ)
        = A ^ 2 * ∫⁻ x, (hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) := hmul
      _ ≤ A ^ 2 * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ‖h k x‖ₑ ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hHL bot_le
      _ = ENNReal.ofReal (d ^ 2 * C₀ ^ 2) * ∫⁻ x, ‖h k x‖ₑ ^ (2 : ℝ) := by
          rw [hAeq, ← ENNReal.ofReal_pow hdpos.le 2, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
  have hlast : (∫⁻ x, ∑ k : Fin K, ‖h k x‖ₑ ^ (2 : ℝ))
      = ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖h k x‖ ^ 2) := by
    refine lintegral_congr fun x => ?_
    have h1 : ∀ k : Fin K, ‖h k x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖h k x‖ ^ 2) := by
      intro k
      rw [ENNReal.rpow_two, enorm_complex_eq_ofReal,
        ENNReal.ofReal_pow (norm_nonneg (h k x))]
    simp only [h1]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg (‖h k x‖))]
  have hKC : (K : ℝ≥0∞) * ENNReal.ofReal (d ^ 2 * C₀ ^ 2)
      = ENNReal.ofReal (d ^ 2 * C₀ ^ 2 * (K : ℝ)) := by
    rw [← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
          ‖∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
            (∫ y : ℝ, h k y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))))‖ₑ) ^ (2 : ℝ)
          ∂(volume : Measure ℝ)
      ≤ ∫⁻ x, (K : ℝ≥0∞) * ∑ k : Fin K,
            (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_mono hpoint
    _ = (K : ℝ≥0∞) * ∫⁻ x, ∑ k : Fin K,
            (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_const_mul' _ _ (ENNReal.natCast_ne_top K)
    _ = (K : ℝ≥0∞) * ∑ k : Fin K, ∫⁻ x,
            (A * hlMax (fun y : ℝ => ‖h k y‖ₑ) x) ^ (2 : ℝ) := by
        rw [lintegral_finsetSum' Finset.univ (fun k _ => (hmeasM k).aemeasurable)]
    _ ≤ (K : ℝ≥0∞) * ∑ k : Fin K,
            ENNReal.ofReal (d ^ 2 * C₀ ^ 2) * ∫⁻ x, ‖h k x‖ₑ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hkbound k) bot_le
    _ = (K : ℝ≥0∞) * ENNReal.ofReal (d ^ 2 * C₀ ^ 2)
          * ∑ k : Fin K, ∫⁻ x, ‖h k x‖ₑ ^ (2 : ℝ) := by
        rw [← Finset.mul_sum, mul_assoc]
    _ = (K : ℝ≥0∞) * ENNReal.ofReal (d ^ 2 * C₀ ^ 2)
          * ∫⁻ x, ∑ k : Fin K, ‖h k x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_finsetSum' Finset.univ (fun k _ => hmeas2 k)]
    _ = (K : ℝ≥0∞) * ENNReal.ofReal (d ^ 2 * C₀ ^ 2)
          * ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖h k x‖ ^ 2) := by rw [hlast]
    _ = ENNReal.ofReal (d ^ 2 * C₀ ^ 2 * (K : ℝ))
          * ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖h k x‖ ^ 2) := by rw [hKC]

end Commons.Analysis.Fourier
