import Mathlib
import Submission.Work.GM.Affine.far_window_defs
import Submission.Work.GM.Affine.integrable_Fhat_sq
import Submission.Work.GM.Affine.fhat_tail_le_of_decay
import Submission.Work.GM.Affine.far_mass_le
import Submission.Work.GM.Affine.summable_int_inv_one_add_abs_pow
import Submission.Work.GM.Affine.Hfun_le_of_large

/-!
# GM §9, region II: analytic inputs for `farTauWin_finset_le_FarMass`

Helper lemmas for `Work.GM.Affine.farTauWin_finset_le_FarMass`:

* `Fhat_measurable`: `Fhat f` is measurable for *every* `f : ℝ → ℝ`;
* `psi1hat_continuous`, `psi1hat_sq_integrable`, `psi1hat_sq_tail_le`: the `L²`-mass of `ψ̂₁`
  is finite and its tail decays like `R^{-6}`;
* `Hfun_le_const`: the *global* pointwise bound `‖H_ℓ(τ)‖ ≤ A` (from the `j = 0` instance of the
  decay hypothesis), valid for all `ℓ, τ`;
* `Hfun_le_of_ball`: the `(j,ε) = (3,1)` decay bound on `|τ| ≤ M₃|ℓ|/2`;
* `farInt_le_uniform`: the resulting uniform decay `∫_{|τ|>2} ‖H_ℓ(τ)‖²‖ψ̂₁(τ)‖² ≤ C/(1+|ℓ|)^6`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `Fhat f` is measurable for every `f : ℝ → ℝ`.  Either `f` is integrable, in which case
`Fhat f` is continuous, or every Fourier integral of `f` vanishes, so that `Fhat f = 0`. -/
lemma Fhat_measurable (f : ℝ → ℝ) : Measurable (Fhat f) := by
  by_cases h : Integrable (fun u : ℝ => (f u : ℂ))
  · have hc : Continuous (Fhat f) :=
      VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner h
    exact hc.measurable
  · have hzero : Fhat f = fun _ => 0 := by
      funext ξ
      rw [Fhat, Real.fourier_eq]
      rw [integral_undef]
      intro hI
      exact h ((Real.fourierIntegral_convergent_iff ξ).mp hI)
    rw [hzero]
    exact measurable_const

/-- `psi1hat K` is continuous (it is the Fourier transform of an `L¹` function). -/
lemma psi1hat_continuous (K : ℝ) : Continuous (psi1hat K) :=
  VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner
    ((psi1_ofReal_contDiff K).continuous.integrable_of_hasCompactSupport
      (psi1_ofReal_hasCompactSupport K))

/-- `‖psi1hat K‖²` is integrable (Plancherel). -/
lemma psi1hat_sq_integrable (K : ℝ) : Integrable (fun τ : ℝ => ‖psi1hat K τ‖ ^ 2) :=
  integrable_fourier_sq_of_continuous_hasCompactSupport (psi1_ofReal_contDiff K).continuous
    (psi1_ofReal_hasCompactSupport K)

/-- **The `L²`-mass of `ψ̂₁`: finiteness and `R^{-6}` decay of the tail.** -/
lemma psi1hat_sq_tail_le (K : ℝ) (hK : 0 < K) :
    ∃ W : ℝ, 0 < W ∧ (∫ τ, ‖psi1hat K τ‖ ^ 2) ≤ W ∧
      ∀ R : ℝ, 1 ≤ R → (∫ τ in {τ : ℝ | R ≤ |τ|}, ‖psi1hat K τ‖ ^ 2) ≤ W / R ^ 6 := by
  obtain ⟨C, hCpos, hCdec⟩ := psi1hat_decay K hK 8
  have hInt : Integrable (fun ξ : ℝ => ‖Fhat (psi1 K) ξ‖ ^ 2) := psi1hat_sq_integrable K
  have hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat (psi1 K) ξ‖ ≤ C * (1 / |ξ|) ^ (4 : ℕ) := by
    intro ξ hξ
    have h1 : ‖Fhat (psi1 K) ξ‖ ≤ C / (1 + |ξ|) ^ 8 := hCdec ξ
    have h2 : C / (1 + |ξ|) ^ 8 ≤ C * (1 / |ξ|) ^ (4 : ℕ) := by
      have hle : |ξ| ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ, sq_nonneg |ξ|]
      have hkey : |ξ| ^ 4 ≤ (1 + |ξ|) ^ 8 := by
        have h := pow_le_pow_left₀ (abs_nonneg ξ) hle 4
        rwa [← pow_mul] at h
      have hfac : (1 : ℝ) ≤ (|ξ| ^ 4)⁻¹ * (1 + |ξ|) ^ 8 := by
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        nlinarith [hkey]
      have hpow : (1 / |ξ|) ^ (4 : ℕ) = (|ξ| ^ 4)⁻¹ := by
        rw [div_pow, show (1 : ℝ) ^ 4 = 1 by norm_num, one_div, inv_eq_one_div]
      have hgoal : C * (|ξ| ^ 4)⁻¹ * (1 + |ξ|) ^ 8 = C * ((|ξ| ^ 4)⁻¹ * (1 + |ξ|) ^ 8) := by
        ring
      rw [hpow, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + |ξ|) ^ 8), hgoal]
      simpa using mul_le_mul_of_nonneg_left hfac hCpos.le
    linarith [h1, h2]
  refine ⟨max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1, by positivity, ?_, ?_⟩
  · have : (∫ τ, ‖psi1hat K τ‖ ^ 2) ≤ max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) :=
      le_max_left _ _
    linarith
  · intro R hR
    have htail := fhat_tail_le_of_decay (f := psi1 K) (B := C) (T := 1) (Y := R) (J := 4)
      (by norm_num) hCpos.le one_pos (lt_of_lt_of_le one_pos hR) hInt hdec
    have htail' : (∫ ξ in {ξ : ℝ | R ≤ |ξ|}, ‖psi1hat K ξ‖ ^ 2)
        ≤ 2 * C ^ 2 / (7 * R ^ 7) := by
      have hEq : (∫ ξ in {ξ : ℝ | R ≤ |ξ|}, ‖Fhat (psi1 K) ξ‖ ^ 2)
          = (∫ ξ in {ξ : ℝ | R ≤ |ξ|}, ‖psi1hat K ξ‖ ^ 2) := rfl
      rw [← hEq]
      refine htail.trans ?_
      norm_num
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
    have hW7 : 2 * C ^ 2 / 7 ≤ max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1 := by
      have := le_max_right (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7)
      linarith
    have hmono : R ^ 6 ≤ R ^ 7 := pow_le_pow_right₀ hR (by norm_num)
    have h1 : 2 * C ^ 2 ≤ 7 * (max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1) := by
      linarith
    have hstep1 : 2 * C ^ 2 * R ^ 6
        ≤ 7 * (max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1) * R ^ 6 :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg hRpos.le 6)
    have hstep2 : 7 * (max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1) * R ^ 6
        ≤ 7 * (max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1) * R ^ 7 := by
      apply mul_le_mul_of_nonneg_left hmono
      have : (0 : ℝ) ≤ 2 * C ^ 2 / 7 := by positivity
      have : (0 : ℝ) ≤ ∫ τ, ‖psi1hat K τ‖ ^ 2 := integral_nonneg (fun τ => sq_nonneg _)
      linarith
    have hfin : 2 * C ^ 2 / (7 * R ^ 7)
        ≤ (max (∫ τ, ‖psi1hat K τ‖ ^ 2) (2 * C ^ 2 / 7) + 1) / R ^ 6 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hstep1, hstep2]
    linarith [htail', hfin]


/-- The `(j,ε) = (3,1)` instance of the decay hypothesis, with the factor `(c 3 1 * Λ)` made
nonnegative. -/
lemma Fhat_le_pow_three {c : ℕ → ℝ → ℝ} {T Λ : ℝ} (hT : 1 ≤ T) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) :
    ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ max (c 3 1 * Λ) 0 * T * (T / |ξ|) ^ 3 := by
  intro ξ hξ
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hξabs : 0 < |ξ| := abs_pos.mpr hξ
  have h := hdec 3 1 one_pos ξ hξ
  rw [Real.rpow_one] at h
  have hV : 0 < T * (T / |ξ|) ^ 3 :=
    mul_pos hTpos (pow_pos (div_pos hTpos hξabs) 3)
  calc ‖Fhat f ξ‖ ≤ c 3 1 * T * (T / |ξ|) ^ 3 * Λ := h
    _ = (c 3 1 * Λ) * (T * (T / |ξ|) ^ 3) := by ring
    _ ≤ max (c 3 1 * Λ) 0 * (T * (T / |ξ|) ^ 3) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hV.le
    _ = max (c 3 1 * Λ) 0 * T * (T / |ξ|) ^ 3 := by ring

/-- **Global pointwise bound on `H_ℓ(τ)`.**

The `(j,ε) = (0,1)` instance of the decay hypothesis bounds `‖F̂f ξ‖` for every `ξ ≠ 0`, and the
single remaining value `F̂f 0` is finite, so

`‖H_ℓ(τ)‖ ≤ (Σ_{m₂∈R2 M₂} m₂) · max (max (c 0 1 * T * Λ) 0) ‖F̂f 0‖`

for *every* `ℓ : ℤ` and *every* `τ : ℝ`. -/
lemma Hfun_le_const {c : ℕ → ℝ → ℝ} {T Λ : ℝ} (hT : 1 ≤ T)
    {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (ℓ : ℤ) (τ : ℝ) :
    ‖Hfun f M₂ M₃ ℓ τ‖ ≤
      (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ := by
  have hFb : ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ := by
    intro ξ hξ
    have h := hdec 0 1 one_pos ξ hξ
    rw [Real.rpow_one] at h
    simp only [pow_zero, mul_one] at h
    exact h.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  have hmain : ‖Hfun f M₂ M₃ ℓ τ‖
      ≤ ∑ m ∈ R2 M₂, (m : ℝ) * max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ := by
    have h1 : ‖Hfun f M₂ M₃ ℓ τ‖
        ≤ ∑ m ∈ R2 M₂, ‖((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ := by
      simpa only [Hfun] using
        (norm_sum_le (R2 M₂)
          (fun m => ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))))
    refine h1.trans (Finset.sum_le_sum (fun m hm => ?_))
    have hmpos : 0 < (m : ℝ) := lt_trans hM₂ (Finset.mem_filter.mp hm).2
    rw [norm_mul, show ‖((m : ℝ) : ℂ)‖ = |(m : ℝ)| from by simp, abs_of_pos hmpos]
    refine mul_le_mul_of_nonneg_left ?_ hmpos.le
    by_cases hu : (m : ℝ) * ((ℓ : ℝ) + τ / M₃) = 0
    · rw [hu]; exact le_max_right _ _
    · exact hFb _ hu
  calc ‖Hfun f M₂ M₃ ℓ τ‖
      ≤ ∑ m ∈ R2 M₂, (m : ℝ) * max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ := hmain
    _ = (∑ m ∈ R2 M₂, (m : ℝ)) * max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ :=
        (Finset.sum_mul (R2 M₂) (fun m : ℤ => (m : ℝ)) _).symm

/-- **`H_ℓ(τ)` is small when `ℓ ≠ 0` and `|τ|/M₃ ≤ |ℓ|/2`.**

This is `Work.GM.Affine.Hfun_le_of_large` with the hypotheses `τ ∈ [-2,2]` and `4 ≤ |ℓ|`
replaced by `|τ| ≤ M₃|ℓ|/2` and `ℓ ≠ 0`; these are exactly what is needed to get
`|ℓ + τ/M₃| ≥ |ℓ|/2` and hence the `(3,1)`-decay bound. -/
theorem Hfun_le_of_ball {c : ℕ → ℝ → ℝ} {T Λ : ℝ} (hT : 1 ≤ T)
    {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (τ : ℝ) (hτ : |τ| ≤ M₃ * |(ℓ : ℝ)| / 2) :
    ‖Hfun f M₂ M₃ ℓ τ‖ ≤
      (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (8 * max (c 3 1 * Λ) 0 * T ^ 4) / |(ℓ : ℝ)| ^ 3 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  let D : ℝ := max (c 3 1 * Λ) 0
  have hDnn : 0 ≤ D := le_max_right _ _
  have hApos : 0 < |(ℓ : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hℓ)
  have hpoint := Fhat_le_pow_three hT hdec
  have hτM : |τ / M₃| ≤ |(ℓ : ℝ)| / 2 := by
    rw [abs_div, abs_of_pos hM₃pos, div_le_iff₀ hM₃pos]
    linarith [hτ]
  have hy_abs : |(ℓ : ℝ)| / 2 ≤ |(ℓ : ℝ) + τ / M₃| := by
    have h1 : |(ℓ : ℝ)| ≤ |(ℓ : ℝ) + τ / M₃| + |τ / M₃| := by
      have h := abs_add_le ((ℓ : ℝ) + τ / M₃) (-(τ / M₃))
      rw [show (ℓ : ℝ) + τ / M₃ + -(τ / M₃) = (ℓ : ℝ) from by ring, abs_neg] at h
      exact h
    linarith
  have hyabs_pos : 0 < |(ℓ : ℝ) + τ / M₃| := lt_of_lt_of_le (by linarith) hy_abs
  have hyne : (ℓ : ℝ) + τ / M₃ ≠ 0 := abs_pos.mp hyabs_pos
  have hterm : ∀ m ∈ R2 M₂,
      (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ≤ 8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3 := by
    intro m hm
    have hm1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1R
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hmyne : (m : ℝ) * ((ℓ : ℝ) + τ / M₃) ≠ 0 := mul_ne_zero hm0 hyne
    have hb := hpoint ((m : ℝ) * ((ℓ : ℝ) + τ / M₃)) hmyne
    have hmm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm1R, sq_nonneg ((m : ℝ) - 1)]
    have hkey : |(ℓ : ℝ)| ^ 3 ≤ 8 * ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3) := by
      have h1 : (|(ℓ : ℝ)| / 2) ^ 3 ≤ |(ℓ : ℝ) + τ / M₃| ^ 3 :=
        pow_le_pow_left₀ (by linarith) hy_abs 3
      have h3 : |(ℓ : ℝ) + τ / M₃| ^ 3 ≤ (m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3 :=
        le_mul_of_one_le_left (pow_nonneg (abs_nonneg _) 3) hmm2
      calc |(ℓ : ℝ)| ^ 3 = 8 * (|(ℓ : ℝ)| / 2) ^ 3 := by ring
        _ ≤ 8 * |(ℓ : ℝ) + τ / M₃| ^ 3 := by linarith
        _ ≤ 8 * ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3) := by linarith
    have hdt : 0 ≤ D * T ^ 4 := mul_nonneg hDnn (pow_nonneg hTpos.le 4)
    have hA3pos : 0 < |(ℓ : ℝ)| ^ 3 := pow_pos hApos 3
    have hden : 0 < (m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3 :=
      mul_pos (pow_pos hmpos 2) (pow_pos hyabs_pos 3)
    have heq : (m : ℝ) * (D * T * (T / |(m : ℝ) * ((ℓ : ℝ) + τ / M₃)|) ^ 3)
        = D * T ^ 4 / ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3) := by
      rw [abs_mul, abs_of_pos hmpos]
      field_simp
    have hle : D * T ^ 4 / ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3)
        ≤ 8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3 := by
      rw [div_le_div_iff₀ hden hA3pos]
      calc D * T ^ 4 * |(ℓ : ℝ)| ^ 3
          ≤ D * T ^ 4 * (8 * ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3)) :=
            mul_le_mul_of_nonneg_left hkey hdt
        _ = 8 * D * T ^ 4 * ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3) := by ring
    calc (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
        ≤ (m : ℝ) * (D * T * (T / |(m : ℝ) * ((ℓ : ℝ) + τ / M₃)|) ^ 3) :=
          mul_le_mul_of_nonneg_left hb hmpos.le
      _ = D * T ^ 4 / ((m : ℝ) ^ 2 * |(ℓ : ℝ) + τ / M₃| ^ 3) := heq
      _ ≤ 8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3 := hle
  have hsum1 : ‖Hfun f M₂ M₃ ℓ τ‖
      ≤ ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ := by
    have h1 : ‖Hfun f M₂ M₃ ℓ τ‖
        ≤ ∑ m ∈ R2 M₂, ‖((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ := by
      simpa only [Hfun] using
        (norm_sum_le (R2 M₂)
          (fun m => ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))))
    refine h1.trans (Finset.sum_le_sum (fun m hm => ?_))
    have hm1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    rw [norm_mul, show ‖((m : ℝ) : ℂ)‖ = |(m : ℝ)| from by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ))]
  have hsum2 : ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
      ≤ (R2 M₂).card * (8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3) := by
    calc ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃))‖
        ≤ ∑ m ∈ R2 M₂, (8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3) := Finset.sum_le_sum hterm
      _ = (R2 M₂).card * (8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((R2 M₂).card : ℝ) ≤ ∑ m ∈ R2 M₂, (m : ℝ) := by
    have h1 : ((R2 M₂).card : ℝ) = ∑ m ∈ R2 M₂, (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1]
    exact Finset.sum_le_sum (fun m hm => by
      have hm1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      exact_mod_cast hm1)
  have hc0 : 0 ≤ 8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDnn) (pow_nonneg hTpos.le 4))
      (pow_nonneg hApos.le 3)
  have hsum3 : (R2 M₂).card * (8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3)
      ≤ (∑ m ∈ R2 M₂, (m : ℝ)) * (8 * D * T ^ 4 / |(ℓ : ℝ)| ^ 3) :=
    mul_le_mul_of_nonneg_right hcard hc0
  refine le_trans hsum1 (le_trans hsum2 hsum3) |>.trans_eq ?_
  rw [show D = max (c 3 1 * Λ) 0 from rfl]
  ring


/-- **The `ℓ`-th far mass decays like `|ℓ|^{-6}`.**

`farInt ℓ = ∫_{|τ|>2} ‖H_ℓ(τ)‖² ‖ψ̂₁(τ)‖² dτ` with `H_ℓ(τ) = Hfun f M₂ M₃ ℓ τ`: under the
Fourier decay hypothesis of GM §9, `farInt ℓ ≤ C/(1+|ℓ|)^6` with a constant `C` uniform in `ℓ`.

The `(j,ε) = (0,1)` instance of `hdec` gives the global bound `‖H_ℓ(τ)‖ ≤ A` (`Hfun_le_const`);
splitting `{|τ| > 2}` into `RegI = {|τ| ≤ M₃|ℓ|/2}` and its complement gives respectively the
`(3,1)`-decay bound (`Hfun_le_of_ball`) and the uniform bound against the `‖ψ̂₁‖²`-mass of
`{|τ| > M₃|ℓ|/2}` (`psi1hat_sq_tail_le`). -/
theorem farInt_le_uniform {c : ℕ → ℝ → ℝ} {K T Λ : ℝ} (hK : 0 < K) (hT : 1 ≤ T)
    {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℤ,
      (∫ τ in (Set.Ioi 2 ∪ Set.Iio (-2)),
          ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) ≤
        C / (1 + |((ℓ : ℤ) : ℝ)|) ^ 6 := by
  obtain ⟨W, hWpos, hWtot, hWtail⟩ := psi1hat_sq_tail_le K hK
  have hIntpsi : Integrable (fun τ : ℝ => ‖psi1hat K τ‖ ^ 2) := psi1hat_sq_integrable K
  have hpsi_meas : Measurable (fun τ : ℝ => ‖psi1hat K τ‖ ^ 2) :=
    ((psi1hat_continuous K).norm).measurable.pow_const 2
  set S0 : ℝ := ∑ m ∈ R2 M₂, (m : ℝ) with hS0
  have hS0nn : 0 ≤ S0 := by
    rw [hS0]
    exact Finset.sum_nonneg (fun m hm => le_of_lt (lt_trans hM₂ (Finset.mem_filter.mp hm).2))
  set A : ℝ := S0 * max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ with hA
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg hS0nn
      (le_trans (le_max_right (c 0 1 * T * Λ) 0) (le_max_left _ _))
  have hHle : ∀ ℓ τ, ‖Hfun f M₂ M₃ ℓ τ‖ ≤ A := by
    intro ℓ τ
    have h := Hfun_le_const (c := c) (T := T) (Λ := Λ) (M₂ := M₂) (M₃ := M₃)
      (f := f) hT hM₂ hdec ℓ τ
    simpa only [hA, hS0] using h
  set far : Set ℝ := Set.Ioi 2 ∪ Set.Iio (-2) with hfar
  have hfar_meas : MeasurableSet far := by
    rw [hfar]; exact measurableSet_Ioi.union measurableSet_Iio
  have hfar_abs : ∀ τ : ℝ, τ ∈ far → 2 < |τ| := by
    intro τ hτ
    rw [hfar] at hτ
    rcases hτ with h | h
    · rw [Set.mem_Ioi] at h
      rwa [abs_of_pos (by linarith : (0 : ℝ) < τ)]
    · rw [Set.mem_Iio] at h
      rw [abs_of_neg (by linarith : τ < 0)]
      linarith
  have hgmeas : ∀ ℓ : ℤ, AEStronglyMeasurable
      (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) volume := by
    intro ℓ
    refine Measurable.aestronglyMeasurable ?_
    have hH : Measurable (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ) := by
      have heq : (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ)
          = fun τ : ℝ => ∑ m ∈ R2 M₂,
              ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃)) := by
        funext τ; simp only [Hfun]
      rw [heq]
      exact Finset.measurable_sum _ (fun m _ => measurable_const.mul
        ((Fhat_measurable f).comp (measurable_const.mul
          (measurable_const.add (measurable_id.div_const M₃)))))
    exact (hH.norm.pow_const 2).mul hpsi_meas
  have hg_int : ∀ ℓ : ℤ, Integrable
      (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) := by
    intro ℓ
    refine Integrable.mono (hIntpsi.const_mul (A ^ 2)) (hgmeas ℓ) ?_
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have h1 : ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hHle ℓ τ) 2
    have h2 : 0 ≤ ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2 := by positivity
    have h3 : 0 ≤ A ^ 2 * ‖psi1hat K τ‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg h3]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  refine ⟨64 * ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W)
    + 262144 * (A ^ 2 * W) + 1, ?_, ?_⟩
  · have hX : 0 ≤ (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W :=
      mul_nonneg (sq_nonneg _) hWpos.le
    have hY : 0 ≤ A ^ 2 * W := mul_nonneg (sq_nonneg _) hWpos.le
    linarith
  · intro ℓ
    set Ll : ℝ := |(ℓ : ℝ)| with hLl
    set Ml : ℝ := max 1 Ll with hMl
    set R : ℝ := max 2 (M₃ * Ll / 2) with hR
    set RegI : Set ℝ := {τ : ℝ | |τ| ≤ M₃ * Ll / 2} with hRegI
    have hRegImeas : MeasurableSet RegI := by
      rw [hRegI]
      exact measurableSet_le continuous_abs.measurable measurable_const
    have hLl0 : 0 ≤ Ll := by rw [hLl]; exact abs_nonneg _
    have hptI : ∀ τ ∈ far ∩ RegI,
        ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
          ≤ ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * ‖psi1hat K τ‖ ^ 2 := by
      intro τ hτ
      have hτI : |τ| ≤ M₃ * Ll / 2 := hτ.2
      by_cases hℓ0 : ℓ = 0
      · exfalso
        have hLl0' : Ll = 0 := by rw [hLl, hℓ0]; simp
        have h1 : |τ| ≤ 0 := by rw [hLl0'] at hτI; simpa using hτI
        have h2 := hfar_abs τ hτ.1
        linarith
      · have hb := Hfun_le_of_ball (c := c) (T := T) (Λ := Λ) (M₂ := M₂) (M₃ := M₃)
          (f := f) hT hM₂ hM₃ hdec ℓ hℓ0 τ (by rw [← hLl]; exact hτI)
        have hMleq : Ml = Ll := by
          rw [hMl]
          refine max_eq_right ?_
          have h1 : (1 : ℤ) ≤ |ℓ| := Int.one_le_abs hℓ0
          have h2 : ((1 : ℤ) : ℝ) ≤ ((|ℓ| : ℤ) : ℝ) := by exact_mod_cast h1
          rw [hLl]
          rw [Int.cast_abs] at h2
          simpa using h2
        have hHsq : ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2
            ≤ (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6 := by
          rw [hMleq]
          calc ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2
              ≤ (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4) / Ll ^ 3) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (by rw [hLl]; exact hb) 2
            _ = (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ll ^ 6 := by
                rw [div_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right hHsq (sq_nonneg _)
    have hIupper : ∫ τ in far ∩ RegI, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
        ≤ ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * W := by
      have hmaj_int : IntegrableOn (fun τ : ℝ =>
          ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * ‖psi1hat K τ‖ ^ 2)
          (far ∩ RegI) := (hIntpsi.const_mul _).integrableOn
      have h2 : ∫ τ in far ∩ RegI,
            ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * ‖psi1hat K τ‖ ^ 2
          = ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6)
              * ∫ τ in far ∩ RegI, ‖psi1hat K τ‖ ^ 2 :=
        integral_const_mul _ _
      have h3 : ∫ τ in far ∩ RegI, ‖psi1hat K τ‖ ^ 2 ≤ W :=
        le_trans (setIntegral_le_integral hIntpsi
          (Filter.Eventually.of_forall (fun τ => sq_nonneg _))) hWtot
      calc ∫ τ in far ∩ RegI, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
          ≤ ∫ τ in far ∩ RegI,
              ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * ‖psi1hat K τ‖ ^ 2 :=
            setIntegral_mono_of_nonneg (fun τ _ => by positivity) hptI hmaj_int
        _ = ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6)
              * ∫ τ in far ∩ RegI, ‖psi1hat K τ‖ ^ 2 := h2
        _ ≤ ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * W :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    have hptII : ∀ τ ∈ far ∩ RegIᶜ,
        ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2 ≤ A ^ 2 * ‖psi1hat K τ‖ ^ 2 := by
      intro τ _
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hHle ℓ τ) 2) (sq_nonneg _)
    have hIIupper : ∫ τ in far ∩ RegIᶜ, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
        ≤ A ^ 2 * (W / R ^ 6) := by
      have hmaj_int : IntegrableOn (fun τ : ℝ => A ^ 2 * ‖psi1hat K τ‖ ^ 2)
          (far ∩ RegIᶜ) := (hIntpsi.const_mul _).integrableOn
      have h1 : ∫ τ in far ∩ RegIᶜ, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
          ≤ ∫ τ in far ∩ RegIᶜ, A ^ 2 * ‖psi1hat K τ‖ ^ 2 :=
        setIntegral_mono_of_nonneg (fun τ _ => by positivity) hptII hmaj_int
      have h2 : ∫ τ in far ∩ RegIᶜ, A ^ 2 * ‖psi1hat K τ‖ ^ 2
          = A ^ 2 * ∫ τ in far ∩ RegIᶜ, ‖psi1hat K τ‖ ^ 2 := integral_const_mul _ _
      have hsub : far ∩ RegIᶜ ⊆ {τ : ℝ | R ≤ |τ|} := by
        intro τ hτ
        have hMI : M₃ * Ll / 2 < |τ| := by
          rw [hRegI] at hτ
          simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hτ
          exact hτ.2
        have h2lt := hfar_abs τ hτ.1
        rw [Set.mem_ofPred_eq, hR]
        exact le_of_lt (max_lt h2lt hMI)
      have h3 : ∫ τ in far ∩ RegIᶜ, ‖psi1hat K τ‖ ^ 2
          ≤ ∫ τ in {τ : ℝ | R ≤ |τ|}, ‖psi1hat K τ‖ ^ 2 :=
        setIntegral_mono_set (hIntpsi.integrableOn)
          (Filter.Eventually.of_forall (fun τ => sq_nonneg _))
          (Filter.Eventually.of_forall hsub)
      have hR1 : (1 : ℝ) ≤ R := by
        rw [hR]
        exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)
      have h4 : ∫ τ in {τ : ℝ | R ≤ |τ|}, ‖psi1hat K τ‖ ^ 2 ≤ W / R ^ 6 := hWtail R hR1
      calc ∫ τ in far ∩ RegIᶜ, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
          ≤ ∫ τ in far ∩ RegIᶜ, A ^ 2 * ‖psi1hat K τ‖ ^ 2 := h1
        _ = A ^ 2 * ∫ τ in far ∩ RegIᶜ, ‖psi1hat K τ‖ ^ 2 := h2
        _ ≤ A ^ 2 * (W / R ^ 6) :=
            mul_le_mul_of_nonneg_left (le_trans h3 h4) (by positivity)
    have hdisj : Disjoint (far ∩ RegI) (far ∩ RegIᶜ) :=
      (disjoint_compl_right (a := RegI)).mono Set.inter_subset_right Set.inter_subset_right
    have hsplit : far = (far ∩ RegI) ∪ (far ∩ RegIᶜ) := by
      ext τ
      constructor
      · intro hτ
        by_cases h : τ ∈ RegI
        · exact Or.inl ⟨hτ, h⟩
        · exact Or.inr ⟨hτ, h⟩
      · rintro (⟨hτ, _⟩ | ⟨hτ, _⟩) <;> exact hτ
    have hsum_eq : ∫ τ in far, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
        = (∫ τ in far ∩ RegI, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
          + (∫ τ in far ∩ RegIᶜ, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) := by
      nth_rewrite 1 [hsplit]
      rw [setIntegral_union hdisj (hfar_meas.inter hRegImeas.compl)
        ((hg_int ℓ).integrableOn) ((hg_int ℓ).integrableOn)]
    have hMlge : (1 + Ll) / 2 ≤ Ml := by
      rw [hMl]
      rcases le_or_gt Ll 1 with h | h
      · exact le_trans (by linarith) (le_max_left _ _)
      · exact le_trans (by linarith) (le_max_right _ _)
    have hInvMl : 1 / Ml ^ 6 ≤ 64 / (1 + Ll) ^ 6 := by
      have h3 : (1 + Ll) ^ 6 / 64 ≤ Ml ^ 6 := by
        have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (1 + Ll) / 2) hMlge 6
        rwa [div_pow, show (2 : ℝ) ^ 6 = 64 by norm_num] at h
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mp h3
      linarith
    have hRge : (1 + Ll) / 4 ≤ R := by
      rw [hR]
      have hmono : max 2 (Ll / 2) ≤ max 2 (M₃ * Ll / 2) := by
        refine max_le_max le_rfl ?_
        have h := mul_le_mul_of_nonneg_right hM₃ hLl0
        linarith
      refine le_trans ?_ hmono
      rcases le_or_gt Ll 1 with h | h
      · exact le_trans (by linarith) (le_max_left _ _)
      · exact le_trans (by linarith) (le_max_right _ _)
    have hInvR : 1 / R ^ 6 ≤ 4096 / (1 + Ll) ^ 6 := by
      have h3 : (1 + Ll) ^ 6 / 4096 ≤ R ^ 6 := by
        have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (1 + Ll) / 4) hRge 6
        rwa [div_pow, show (4 : ℝ) ^ 6 = 4096 by norm_num] at h
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)).mp h3
      linarith
    have hXnn : 0 ≤ (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W :=
      mul_nonneg (sq_nonneg _) hWpos.le
    have hYnn : 0 ≤ A ^ 2 * W := mul_nonneg (sq_nonneg _) hWpos.le
    calc ∫ τ in far, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2
        = (∫ τ in far ∩ RegI, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
          + (∫ τ in far ∩ RegIᶜ, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) := hsum_eq
      _ ≤ ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * W
            + A ^ 2 * (W / R ^ 6) := add_le_add hIupper hIIupper
      _ ≤ (64 * ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W)
            + 262144 * (A ^ 2 * W)) / (1 + Ll) ^ 6 := by
        have hterm1 : ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * W
            ≤ 64 * ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W) / (1 + Ll) ^ 6 := by
          calc ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 / Ml ^ 6) * W
              = (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * (1 / Ml ^ 6) * W := by ring
            _ ≤ (S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * (64 / (1 + Ll) ^ 6) * W := by
                refine mul_le_mul_of_nonneg_right ?_ hWpos.le
                exact mul_le_mul_of_nonneg_left hInvMl (sq_nonneg _)
            _ = 64 * ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W)
                  / (1 + Ll) ^ 6 := by ring
        have hterm2 : A ^ 2 * (W / R ^ 6) ≤ 262144 * (A ^ 2 * W) / (1 + Ll) ^ 6 := by
          calc A ^ 2 * (W / R ^ 6) = A ^ 2 * W * (1 / R ^ 6) := by ring
            _ ≤ A ^ 2 * W * (4096 / (1 + Ll) ^ 6) := mul_le_mul_of_nonneg_left hInvR hYnn
            _ = 4096 * (A ^ 2 * W) / (1 + Ll) ^ 6 := by ring
            _ ≤ 262144 * (A ^ 2 * W) / (1 + Ll) ^ 6 := by
                refine div_le_div_of_nonneg_right ?_ (by positivity)
                exact mul_le_mul_of_nonneg_right (by norm_num) hYnn
        rw [add_div]
        linarith
      _ ≤ (64 * ((S0 * (8 * max (c 3 1 * Λ) 0 * T ^ 4)) ^ 2 * W)
            + 262144 * (A ^ 2 * W) + 1) / (1 + Ll) ^ 6 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        linarith


/-- **Integrability of one `ℓ`-summand of the far mass.**

The global bound `‖H_ℓ(τ)‖ ≤ A` (`Hfun_le_const`, from the `(j,ε) = (0,1)` instance of the decay
hypothesis) holds for *every* `τ`, so `‖H_ℓ(τ)‖²‖ψ̂₁(τ)‖² ≤ A²‖ψ̂₁(τ)‖²` pointwise and
`‖ψ̂₁‖²` is integrable (`psi1hat_sq_integrable`). -/
lemma integrable_farSummand {c : ℕ → ℝ → ℝ} {K T Λ : ℝ} (hT : 1 ≤ T)
    {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) (ℓ : ℤ) :
    Integrable (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) := by
  set A : ℝ := (∑ m ∈ R2 M₂, (m : ℝ)) * max (max (c 0 1 * T * Λ) 0) ‖Fhat f 0‖ with hA
  have hHle : ∀ τ, ‖Hfun f M₂ M₃ ℓ τ‖ ≤ A := fun τ => by
    have h := Hfun_le_const (c := c) (T := T) (Λ := Λ) (M₂ := M₂) (M₃ := M₃) (f := f)
      hT hM₂ hdec ℓ τ
    simpa only [hA] using h
  have hpsi_meas : Measurable (fun τ : ℝ => ‖psi1hat K τ‖ ^ 2) :=
    ((psi1hat_continuous K).norm).measurable.pow_const 2
  have hmeas : AEStronglyMeasurable
      (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) volume := by
    refine Measurable.aestronglyMeasurable ?_
    have hH : Measurable (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ) := by
      have heq : (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ)
          = fun τ : ℝ => ∑ m ∈ R2 M₂,
              ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃)) := by
        funext τ; simp only [Hfun]
      rw [heq]
      exact Finset.measurable_sum _ (fun m _ => measurable_const.mul
        ((Fhat_measurable f).comp (measurable_const.mul
          (measurable_const.add (measurable_id.div_const M₃)))))
    exact (hH.norm.pow_const 2).mul hpsi_meas
  refine Integrable.mono ((psi1hat_sq_integrable K).const_mul (A ^ 2)) hmeas ?_
  refine Filter.Eventually.of_forall (fun τ => ?_)
  have h1 : ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hHle τ) 2
  have h2 : 0 ≤ ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2 := by positivity
  have h3 : 0 ≤ A ^ 2 * ‖psi1hat K τ‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg h3]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

end

end Work.GM.Affine
