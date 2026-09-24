import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.plancherel_continuous
import Submission.Work.GM.Affine.assembly_aux
import Submission.Work.GM.Affine.psiSmooth_fhat_lower_bound
import Submission.Work.GM.Affine.smoothed_psiSmooth_fourier

/-!
# GM §9: from the high-tail bound to the `L²`-comparison `∫f² ≤ C T^{2δ} ∫f̃²`

This file assembles the elementary (measure-theoretic) part of the reduction

  `∫ f² ≤ C' T^{2δ} ∫ f̃²`,  where `f̃ = smoothed psiSmooth T f`,

from the single analytic input `hcrux`: a bound for the *high-frequency tail*
`∫_{ξ > T/2} ‖Fhat f ξ‖²` by `C T^{2δ}` times the mass on the middle range
`∫_{-(T/2) < ξ ≤ T/2} ‖Fhat f ξ‖²`.

The ingredients:

* Plancherel for `f` and for `f̃` (`plancherel_continuous`), turning the `u`-integrals into
  `ξ`-integrals of `‖Fhat ·‖²`;
* conjugate symmetry `Fhat f (-ξ) = conj (Fhat f ξ)` for a real-valued `f`, hence
  `‖Fhat f (-ξ)‖ = ‖Fhat f ξ‖` — this reflects the negative tail onto the positive one;
* the pointwise lower bound `‖Fhat psiSmooth (ξ/T)‖² ≥ 1/2` on the critical range `|ξ| ≤ T/2`
  (`psiSmooth_fhat_lower_bound`) together with the convolution identity
  `Fhat f̃ ξ = Fhat psiSmooth (ξ/T) · Fhat f ξ` (`smoothed_psiSmooth_fourier`);
* the trivial remark `C T^{2δ} ≤ (1 + 2 max C 0) T^{2δ}` for `T ≥ 1`, `δ > 0`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.GM.Affine

noncomputable section

/-! ### Conjugate symmetry of `Fhat` for a real-valued function -/

/-- `𝓕 (conj ∘ g) ξ = conj (𝓕 g (-ξ))` for any `g : ℝ → ℂ`. -/
lemma fourier_conj_neg' (g : ℝ → ℂ) (ξ : ℝ) :
    FourierTransform.fourier (fun u => (starRingEnd ℂ) (g u)) ξ
      = (starRingEnd ℂ) (FourierTransform.fourier g (-ξ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- **Conjugate symmetry of the Fourier transform of a real function**:
`Fhat f (-ξ) = conj (Fhat f ξ)`. -/
lemma Fhat_neg_eq_conj (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f (-ξ) = (starRingEnd ℂ) (Fhat f ξ) := by
  have h := fourier_conj_neg' (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ
  have hfun : (fun u : ℝ => (starRingEnd ℂ) (((f u : ℝ) : ℂ)))
      = fun u : ℝ => ((f u : ℝ) : ℂ) := by
    funext u; exact Complex.conj_ofReal _
  rw [hfun] at h
  unfold Fhat
  rw [h, Complex.conj_conj]

/-- The modulus of `Fhat f` is even for a real-valued `f`. -/
lemma norm_Fhat_neg (f : ℝ → ℝ) (ξ : ℝ) : ‖Fhat f (-ξ)‖ = ‖Fhat f ξ‖ := by
  rw [Fhat_neg_eq_conj]
  simp

/-- The square modulus of `Fhat f` is even for a real-valued `f`. -/
lemma sq_norm_Fhat_neg (f : ℝ → ℝ) (ξ : ℝ) :
    ‖Fhat f (-ξ)‖ ^ 2 = ‖Fhat f ξ‖ ^ 2 := by
  rw [norm_Fhat_neg]

/-- The Fourier transform of an integrable function is continuous. -/
lemma continuous_Fhat {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) : Continuous (Fhat f) := by
  unfold Fhat
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf.ofReal

/-! ### Splitting an integral over `ℝ` into the middle range and the two tails -/

/-- For `a ≥ 0` and an integrable `g`, the integral over `ℝ` splits into the middle range
`(-a, a]` and the two half-lines `(-∞, -a]` and `(a, ∞)`. -/
lemma integral_eq_Ioc_add_tails {g : ℝ → ℝ} (hInt : Integrable g) {a : ℝ} (ha : 0 ≤ a) :
    ∫ ξ, g ξ = (∫ ξ in Set.Ioc (-a) a, g ξ)
      + ((∫ ξ in Set.Iic (-a), g ξ) + (∫ ξ in Set.Ioi a, g ξ)) := by
  have hA : MeasurableSet (Set.Ioc (-a) a) := measurableSet_Ioc
  have hdisj : Disjoint (Set.Iic (-a)) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_Iic] at hx
    simp only [Set.mem_Ioi] at hy
    linarith
  have h2 : (∫ ξ in (Set.Ioc (-a) a)ᶜ, g ξ)
      = (∫ ξ in Set.Iic (-a), g ξ) + (∫ ξ in Set.Ioi a, g ξ) := by
    rw [Set.compl_Ioc,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hInt.integrableOn hInt.integrableOn]
  rw [← h2]
  exact (MeasureTheory.integral_add_compl (s := Set.Ioc (-a) a) measurableSet_Ioc hInt).symm

/-- For an even `g`, the integral over the negative half-line `(-∞, -a]` equals the integral over
the positive half-line `(a, ∞)`. -/
lemma setIntegral_Iic_neg_eq_Ioi {g : ℝ → ℝ} (h : ∀ x, g (-x) = g x) (a : ℝ) :
    (∫ ξ in Set.Iic (-a), g ξ) = ∫ ξ in Set.Ioi a, g ξ := by
  have h1 : (∫ x in Set.Ioi a, g (-x)) = ∫ x in Set.Iic (-a), g x := integral_comp_neg_Ioi a g
  rw [show (fun x => g (-x)) = g from funext h] at h1
  exact h1.symm

/-! ### An arithmetic absorption of the constant -/

/-- For `T ≥ 1` and `δ > 0` the factor `1 + 2 C T^{2δ}` is dominated by
`(1 + 2 max C 0) T^{2δ}`, so that the "trivial" addend `1` can be absorbed into `T^{2δ}`
without ever making the constant negative. -/
lemma one_add_two_mul_le_max {C T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) :
    1 + 2 * C * T ^ (2 * δ) ≤ (1 + 2 * max C 0) * T ^ (2 * δ) := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hTδ : (1:ℝ) ≤ T ^ (2 * δ) := Real.one_le_rpow hT (by linarith)
  have hpos : (0:ℝ) < T ^ (2 * δ) := Real.rpow_pos_of_pos hT0 _
  rcases le_or_gt C 0 with hC | hC
  · have h1 : C * T ^ (2 * δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hpos.le
    rw [max_eq_right hC]
    nlinarith
  · have h1 : 0 ≤ C * T ^ (2 * δ) := mul_nonneg hC.le hpos.le
    rw [max_eq_left hC.le]
    nlinarith [hTδ]

/-! ### The assembly -/

theorem f_sq_le_smoothed_sq_of_high_tail {C₀ T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    {c : ℕ → ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {C : ℝ}
    (hcrux : ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2
          ≤ C * T ^ (2 * δ) * ∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ u, (f u) ^ 2 ≤ C' * T ^ (2 * δ) * ∫ u, (smoothed psiSmooth T f u) ^ 2 := by
  refine ⟨2 * (1 + 2 * max C 0), by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛpos hdec hΛ
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  obtain ⟨hsmc, hsmcs, hsmF⟩ := smoothed_psiSmooth_fourier hTpos hf hcs
  have hsmint : Integrable (smoothed psiSmooth T f) := hsmc.integrable_of_hasCompactSupport hsmcs
  -- Plancherel for `f` and for `f̃`
  have hplanf : (∫ u, (f u) ^ 2) = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := by
    have h := plancherel_continuous (fun u : ℝ => ((f u : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hf) (hcs.comp_left (g := Complex.ofReal) (by simp))
    have hL : (∫ x, ‖(fun u : ℝ => ((f u : ℝ) : ℂ)) x‖ ^ 2) = ∫ u, (f u) ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp
    rw [hL] at h
    have hR : (∫ ξ, ‖FourierTransform.fourier (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ‖ ^ 2)
        = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := rfl
    rw [hR] at h
    exact h
  have hplang : (∫ u, (smoothed psiSmooth T f u) ^ 2)
      = ∫ ξ, ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2 := by
    have h := plancherel_continuous (fun u : ℝ => ((smoothed psiSmooth T f u : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hsmc) (hsmcs.comp_left (g := Complex.ofReal) (by simp))
    have hL : (∫ x, ‖(fun u : ℝ => ((smoothed psiSmooth T f u : ℝ) : ℂ)) x‖ ^ 2)
        = ∫ u, (smoothed psiSmooth T f u) ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp
    rw [hL] at h
    have hR : (∫ ξ, ‖FourierTransform.fourier
          (fun u : ℝ => ((smoothed psiSmooth T f u : ℝ) : ℂ)) ξ‖ ^ 2)
        = ∫ ξ, ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2 := rfl
    rw [hR] at h
    exact h
  by_cases hf0 : (∫ u, (f u) ^ 2) = 0
  · -- `f` vanishes: the claim is trivial
    rw [hf0]
    have h3 : (0 : ℝ) ≤ 2 * (1 + 2 * max C 0) := by positivity
    have h4 : (0 : ℝ) ≤ T ^ (2 * δ) := (Real.rpow_pos_of_pos hTpos _).le
    have h5 : (0 : ℝ) ≤ ∫ u, (smoothed psiSmooth T f u) ^ 2 :=
      integral_nonneg (fun u => sq_nonneg _)
    positivity
  · -- integrability of the two frequency densities
    have hIntg : Integrable (fun ξ => ‖Fhat f ξ‖ ^ 2) := by
      by_contra hcon
      have hz : (∫ ξ, ‖Fhat f ξ‖ ^ 2) = 0 := integral_undef hcon
      rw [hz] at hplanf
      exact hf0 hplanf
    have hIntg' : Integrable (fun ξ => ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2) := by
      refine Integrable.mono' hIntg ?_ ?_
      · exact (((continuous_Fhat hsmint).norm).pow 2).aestronglyMeasurable
      · filter_upwards with ξ
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hb : ‖Fhat (smoothed psiSmooth T f) ξ‖ ≤ ‖Fhat f ξ‖ := by
          rw [hsmF ξ, norm_mul]
          calc ‖Fhat psiSmooth (ξ / T)‖ * ‖Fhat f ξ‖
              ≤ 1 * ‖Fhat f ξ‖ :=
                mul_le_mul_of_nonneg_right (norm_Fhat_le_one psiSmooth_nonneg psiSmooth_integral _)
                  (norm_nonneg _)
            _ = ‖Fhat f ξ‖ := one_mul _
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    -- splitting `∫_ℝ` into the middle range plus the two tails
    have hsplit : (∫ ξ, ‖Fhat f ξ‖ ^ 2)
        = (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
          + ((∫ ξ in Set.Iic (-(T / 2)), ‖Fhat f ξ‖ ^ 2)
              + (∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2)) :=
      integral_eq_Ioc_add_tails hIntg (by linarith)
    have hsymm : (∫ ξ in Set.Iic (-(T / 2)), ‖Fhat f ξ‖ ^ 2)
        = ∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2 :=
      setIntegral_Iic_neg_eq_Ioi (fun x => sq_norm_Fhat_neg f x) (T / 2)
    -- the analytic input: the positive tail is controlled by the middle range
    have hB := hcrux T hT f hf hfnn hsupp Λ hΛpos hdec hΛ
    have hB' : (∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2)
        ≤ (C * T ^ (2 * δ)) * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) := hB
    -- the middle range is controlled by `∫ f̃²`
    have hS : (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
        ≤ 2 * ∫ u, (smoothed psiSmooth T f u) ^ 2 := by
      have hpt : ∀ ξ ∈ Set.Ioc (-(T / 2)) (T / 2),
          ‖Fhat f ξ‖ ^ 2 ≤ 2 * ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2 := by
        intro ξ hξ
        have hξa : |ξ| ≤ T / 2 := by
          rw [Set.mem_Ioc] at hξ
          rw [abs_le]
          exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
        have hξT : |ξ / T| ≤ 1 / 2 := by
          rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]
          linarith [hξa]
        have hlow : (1 : ℝ) / 2 ≤ ‖Fhat psiSmooth (ξ / T)‖ ^ 2 :=
          psiSmooth_fhat_lower_bound hξT
        rw [hsmF ξ, norm_mul, mul_pow]
        nlinarith [hlow, sq_nonneg ‖Fhat f ξ‖, sq_nonneg ‖Fhat psiSmooth (ξ / T)‖]
      have hmono := MeasureTheory.setIntegral_mono_on
        (s := Set.Ioc (-(T / 2)) (T / 2))
        (f := fun ξ => ‖Fhat f ξ‖ ^ 2)
        (g := fun ξ => 2 * ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2)
        hIntg.integrableOn (hIntg'.const_mul 2).integrableOn measurableSet_Ioc hpt
      have h2 : (∫ ξ in Set.Ioc (-(T / 2)) (T / 2),
            (fun ξ => 2 * ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2) ξ)
          = 2 * ∫ ξ in Set.Ioc (-(T / 2)) (T / 2),
              ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2 :=
        MeasureTheory.integral_const_mul 2 _
      have h3 : (∫ ξ in Set.Ioc (-(T / 2)) (T / 2),
            ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2)
          ≤ ∫ ξ, ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2 :=
        MeasureTheory.setIntegral_le_integral hIntg'
          (Filter.Eventually.of_forall (fun ξ => sq_nonneg _))
      calc (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
          ≤ (∫ ξ in Set.Ioc (-(T / 2)) (T / 2),
              (fun ξ => 2 * ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2) ξ) := hmono
        _ = 2 * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2),
              ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2) := h2
        _ ≤ 2 * (∫ ξ, ‖Fhat (smoothed psiSmooth T f) ξ‖ ^ 2) := by linarith [h3]
        _ = 2 * ∫ u, (smoothed psiSmooth T f u) ^ 2 := by rw [hplang]
    -- assembly
    have hSnn : 0 ≤ (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) :=
      integral_nonneg (fun ξ => sq_nonneg _)
    have hmax := one_add_two_mul_le_max (C := C) (T := T) (δ := δ) hT1 hδ
    have hnonneg : (0 : ℝ) ≤ (1 + 2 * max C 0) * T ^ (2 * δ) :=
      mul_nonneg (by positivity) (Real.rpow_pos_of_pos hTpos _).le
    have hstep2 : (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
          + 2 * (∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2)
        ≤ (1 + 2 * (C * T ^ (2 * δ)))
            * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) := by
      nlinarith [hB', hSnn]
    have hstep3 : (1 + 2 * (C * T ^ (2 * δ)))
            * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
        ≤ ((1 + 2 * max C 0) * T ^ (2 * δ))
            * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hmax hSnn
      nlinarith [h]
    have hstep4 : ((1 + 2 * max C 0) * T ^ (2 * δ))
            * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
        ≤ ((1 + 2 * max C 0) * T ^ (2 * δ)) * (2 * ∫ u, (smoothed psiSmooth T f u) ^ 2) :=
      mul_le_mul_of_nonneg_left hS hnonneg
    have hfinal : (∫ ξ, ‖Fhat f ξ‖ ^ 2)
        ≤ 2 * (1 + 2 * max C 0) * T ^ (2 * δ)
            * ∫ u, (smoothed psiSmooth T f u) ^ 2 := by
      have h1 : (∫ ξ, ‖Fhat f ξ‖ ^ 2)
          = (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
            + 2 * (∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2) := by
        rw [hsplit, hsymm]
        ring
      calc (∫ ξ, ‖Fhat f ξ‖ ^ 2)
          = (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
            + 2 * (∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2) := h1
        _ ≤ (1 + 2 * (C * T ^ (2 * δ)))
            * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) := hstep2
        _ ≤ ((1 + 2 * max C 0) * T ^ (2 * δ))
            * (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2) := hstep3
        _ ≤ ((1 + 2 * max C 0) * T ^ (2 * δ)) * (2 * ∫ u, (smoothed psiSmooth T f u) ^ 2) :=
            hstep4
        _ = 2 * (1 + 2 * max C 0) * T ^ (2 * δ)
            * ∫ u, (smoothed psiSmooth T f u) ^ 2 := by ring
    rw [hplanf]
    exact hfinal

end

end Work.GM.Affine
