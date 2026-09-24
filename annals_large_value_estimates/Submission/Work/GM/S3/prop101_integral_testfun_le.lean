import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.RtildeSq_continuous

/-!
# Mass of the §10 test function (GM Prop 10.1, "`∫ f ≲ ∫_{1/16}^{16} ‖R‖²`")

This file proves `Work.GM.S3.prop101_integral_testfun_le`: for the test function
`f = testfun N W B ψ₁ ψ₂ ψ' = ψ' · R̃²` of GM Proposition 10.1,

`∫_ℝ f ≤ C · K`

with a constant `C` depending only on the fixed bumps `ψ₁, ψ₂, ψ'`, uniformly in `N, W, B` and in
every `K` dominating `∫_{1/16}^{16} ‖R(W, v)‖² dv`.

The proof is a Fubini (Tonelli) argument, formalised through convolution.  Writing
`g u' = ψ₂ u' ‖R(W,u')‖²` (continuous, compactly supported, hence integrable) and
`k t = (N B) ψ₁ ((N B) t)`, the smoothing of GM (7.5) is the convolution

`R̃²(u) = ∫ u', k (u - u') g u' = (g ⋆ k) u`,

so `MeasureTheory.integral_convolution` gives

`∫_u R̃²(u) = (∫ g) · (∫ k) ≤ (∫ g) · (max (∫ ψ₁) 1)`

because `∫ k = (N B) ∫ ψ₁((N B)·) = (N B)|(N B)⁻¹| ∫ ψ₁ ≤ ∫ ψ₁` (the substitution
`x = (N B) t` of `MeasureTheory.Measure.integral_comp_mul_left`).  Finally `ψ₂` is supported in
`[1/16, 16]` (by `IsBumpAtOne ψ₂ 16`), so `∫ g ≤ (sup ψ₂) ∫_{1/16}^{16} ‖R(W,v)‖² dv ≤ c₂ K`, and
multiplying by `ψ'` costs only `sup ψ' ≤ c₃`.
-/

namespace Work.GM.S3

open MeasureTheory Finset
open scoped Convolution

noncomputable section

/-- The kernel `t ↦ A ψ (A t)` of the smoothing is integrable: it is continuous and compactly
supported (`supp ⊆ [-C₀/|A|, C₀/|A|]`, and it vanishes identically when `A = 0`). -/
theorem prop101_integrable_scaled_bump {ψ : ℝ → ℝ} {C₀ : ℝ} (hψ : IsBumpAtZero ψ C₀) (A : ℝ) :
    Integrable (fun t : ℝ => A * ψ (A * t)) := by
  have hcont : Continuous (fun t : ℝ => A * ψ (A * t)) :=
    continuous_const.mul (hψ.1.continuous.comp (continuous_const.mul continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-(C₀ / |A|)) (C₀ / |A|)) isCompact_Icc ?_
  intro t ht
  by_cases hA : A = 0
  · simp [hA]
  · have hC₀0 : 0 ≤ C₀ := by
      have := hψ.2.2.1 0 (by rw [hψ.2.2.2.1]; norm_num)
      simpa using this
    have hdiv : 0 ≤ C₀ / |A| := div_nonneg hC₀0 (abs_nonneg A)
    have hAt : C₀ / |A| < |t| := by
      rcases lt_or_ge t (-(C₀ / |A|)) with h | h
      · have habs : |t| = -t := abs_of_neg (by linarith)
        linarith
      · have h2 : C₀ / |A| < t := by
          by_contra hc
          exact ht (Set.mem_Icc.mpr ⟨h, le_of_not_gt hc⟩)
        have habs : |t| = t := abs_of_pos (by linarith)
        linarith
    have hne : ψ (A * t) = 0 := by
      by_contra hne
      have h1 : |A * t| ≤ C₀ := hψ.2.2.1 (A * t) hne
      have h2 : |A * t| = |A| * |t| := abs_mul A t
      have hApos : 0 < |A| := abs_pos.mpr hA
      have h3 : |A| * (C₀ / |A|) < |A| * |t| := mul_lt_mul_of_pos_left hAt hApos
      have h4 : |A| * (C₀ / |A|) = C₀ := by field_simp
      linarith [h1, h2, h3, h4]
    rw [hne, mul_zero]

/-- `∫_t A ψ (A t) ≤ ∫ ψ` for `A ≥ 0` and `ψ ≥ 0`: the substitution `x = A t` gives
`= A |A⁻¹| ∫ ψ ≤ ∫ ψ`. -/
theorem prop101_integral_scaled_bump_le {ψ : ℝ → ℝ} {C₀ : ℝ} (hψ : IsBumpAtZero ψ C₀) {A : ℝ}
    (hA : 0 ≤ A) : ∫ t : ℝ, A * ψ (A * t) ≤ ∫ x : ℝ, ψ x := by
  have hnonneg : 0 ≤ ∫ x : ℝ, ψ x := integral_nonneg hψ.2.1
  have h1 : ∫ t : ℝ, A * ψ (A * t) = A * ∫ t : ℝ, ψ (A * t) := integral_const_mul A _
  have h2 : ∫ t : ℝ, ψ (A * t) = |A⁻¹| * ∫ y : ℝ, ψ y := by
    rw [MeasureTheory.Measure.integral_comp_mul_left ψ A, smul_eq_mul]
  have h3 : A * |A⁻¹| ≤ 1 := by
    rcases eq_or_lt_of_le hA with h | h
    · rw [← h]; simp
    · rw [abs_of_pos (inv_pos.mpr h), mul_inv_cancel₀ h.ne']
  rw [h1, h2]
  calc A * (|A⁻¹| * ∫ y : ℝ, ψ y) = (A * |A⁻¹|) * ∫ y : ℝ, ψ y := by ring
    _ ≤ 1 * ∫ y : ℝ, ψ y := mul_le_mul_of_nonneg_right h3 hnonneg
    _ = ∫ y : ℝ, ψ y := one_mul _

/-- The weight `u ↦ ψ₂ u ‖R(W,u)‖²` is integrable (continuous with compact support). -/
theorem prop101_integrable_gSq {ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₂ : IsBumpAtOne ψ₂ C₀) (W : Finset ℝ) :
    Integrable (fun u : ℝ => ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) := by
  have hgcont : Continuous (fun u : ℝ => ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) :=
    gSq_continuous ψ₂ C₀ hC₀ h₂ W
  have hgcs : HasCompactSupport (fun u : ℝ => ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) := by
    refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc fun x hx => ?_
    have hx0 : ψ₂ x = 0 := by
      by_contra hne
      exact hx (h₂.2.2.1 x hne)
    simp [hx0]
  exact hgcont.integrable_of_hasCompactSupport hgcs

/-- The smoothing `R̃²` of GM (7.5) is the convolution of the weight `ψ₂‖R‖²` with the kernel
`t ↦ (N B) ψ₁((N B) t)`. -/
theorem prop101_RtildeSq_eq_convolution (W : Finset ℝ) (N : ℕ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) :
    (fun u : ℝ => RtildeSq W N B ψ₁ ψ₂ u)
      = MeasureTheory.convolution (fun u : ℝ => ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2)
          (fun t : ℝ => (N : ℝ) * B * ψ₁ ((N : ℝ) * B * t))
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume := by
  funext u
  rw [RtildeSq, MeasureTheory.convolution_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  ring

/-- **Fubini for the smoothing**: `∫_ℝ R̃² = (∫ ψ₂ ‖R‖²) · ∫_t (N B) ψ₁((N B) t)`. -/
theorem prop101_integral_RtildeSq_eq (W : Finset ℝ) (N : ℕ) (B : ℝ) {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) :
    ∫ u : ℝ, RtildeSq W N B ψ₁ ψ₂ u
      = (∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2)
          * ∫ t : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * t) := by
  rw [prop101_RtildeSq_eq_convolution W N B ψ₁ ψ₂,
    MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (prop101_integrable_gSq (C₀ := 16) (by norm_num) hψ₂ W)
      (prop101_integrable_scaled_bump hψ₁ ((N : ℝ) * B))]
  rfl

/-- **The weight integral is bounded by the `L²` mass of `R` on `[1/16,16]`**: since `ψ₂` is
supported in `[1/16,16]` and bounded by `c`, `∫ ψ₂ u ‖R u‖² ≤ c ∫_{1/16}^{16} ‖R v‖² dv`. -/
theorem prop101_integral_gSq_le_interval {ψ₂ : ℝ → ℝ} {c : ℝ} (hc : ∀ x, ψ₂ x ≤ c)
    (hnn : ∀ x, 0 ≤ ψ₂ x) (hsupp : ∀ x, ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 16 : ℝ) 16)
    (W : Finset ℝ) :
    ∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2
      ≤ c * ∫ v in (1 / 16 : ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 2 := by
  have hpt : ∀ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 ≤
      c * (Set.Icc (1 / 16 : ℝ) 16).indicator (fun v => ‖Submission.GM.Rfun W v‖ ^ 2) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (1 / 16 : ℝ) 16
    · rw [Set.indicator_of_mem hu]
      exact mul_le_mul_of_nonneg_right (hc u) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hu, mul_zero]
      have hz : ψ₂ u = 0 := by
        by_contra hne
        exact hu (hsupp u hne)
      rw [hz, zero_mul]
  have hcont : ContinuousOn (fun v : ℝ => ‖Submission.GM.Rfun W v‖ ^ 2)
      (Set.Icc (1 / 16 : ℝ) 16) := by
    refine ((Rfun_continuousOn_Ioi W).mono ?_).norm.pow 2
    intro x hx
    exact lt_of_lt_of_le (by norm_num) hx.1
  have hint : Integrable (fun u : ℝ => c * (Set.Icc (1 / 16 : ℝ) 16).indicator
      (fun v => ‖Submission.GM.Rfun W v‖ ^ 2) u) :=
    (((hcont.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc).const_mul c)
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun u => mul_nonneg (hnn u) (sq_nonneg _)) hint
    (Filter.Eventually.of_forall hpt)
  rwa [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    at hmain

/-- **Mass of the §10 test function** `f = testfun N W B ψ₁ ψ₂ ψ' = ψ'·RtildeSq W N B ψ₁ ψ₂`, with the constant *uniform* in `N, W, B, K`.  Since `RtildeSq u = ∫ (N B) ψ₁ ((N B)(u-u')) ψ₂ u' ‖Rfun W u'‖² du'`, Fubini for the non-negative kernel gives `∫_ℝ RtildeSq ≤ (∫ψ₁)·∫ ψ₂ u ‖Rfun W u‖² du ≤ (∫ψ₁)(sup ψ₂) ∫_{1/16}^{16}‖Rfun W v‖² dv` (as `supp ψ₂ ⊆ [1/16,16]`, from `IsBumpAtOne ψ₂ 16`), and multiplying by `ψ'` costs `sup ψ'` (finite: `ψ'` is bounded by its `j = 0` derivative bound).  Hence for some absolute `C > 0` (depending only on `ψ₁, ψ₂, ψ'`), `∫_ℝ f ≤ C·K` whenever `0 ≤ N B` and `∫_{1/16}^{16}‖Rfun W v‖² dv ≤ K`. -/
theorem prop101_integral_testfun_le (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hψ₁ : IsBumpAtZero ψ₁ 16)
    (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (W : Finset ℝ) (B K : ℝ),
      0 ≤ (N : ℝ) * B → (∫ v in (1 / 16 : ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ K) →
      ∫ u, testfun N W B ψ₁ ψ₂ ψ' u ≤ C * K := by
  -- the `j = 0` derivative bounds give the sup-norms
  obtain ⟨c₃, hc₃nn, hc₃bd⟩ := hψ'.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc₃bd
  obtain ⟨c₂, hc₂nn, hc₂bd⟩ := hψ₂.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc₂bd
  have hc₃1 : 1 ≤ c₃ := by
    have h := hc₃bd 1
    rw [hψ'.2.2.2.1] at h
    simpa using h
  have hc₂1 : 1 ≤ c₂ := by
    have h := hc₂bd 1
    rw [hψ₂.2.2.2.1] at h
    simpa using h
  have hψ'nn : ∀ x, 0 ≤ ψ' x := hψ'.2.1
  have hψ'acc : ∀ x, ψ' x ≤ c₃ := fun x => le_trans (le_abs_self _) (hc₃bd x)
  have hψ₂le : ∀ x, ψ₂ x ≤ c₂ := fun x => le_trans (le_abs_self _) (hc₂bd x)
  refine ⟨c₃ * max (∫ x : ℝ, ψ₁ x) 1 * c₂, ?_, fun N W B K hNB hK => ?_⟩
  · have h1 : 0 < max (∫ x : ℝ, ψ₁ x) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h2 : 0 < c₃ := lt_of_lt_of_le one_pos hc₃1
    have h3 : 0 < c₂ := lt_of_lt_of_le one_pos hc₂1
    positivity
  -- `K ≥ 0`, from the hypothesis that it dominates a non-negative interval integral
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ ∫ v in (1 / 16 : ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => sq_nonneg _)
    linarith
  -- non-negativity of the smoothing
  have hRtSqnn : ∀ u : ℝ, 0 ≤ RtildeSq W N B ψ₁ ψ₂ u := fun u =>
    integral_nonneg fun u' =>
      mul_nonneg (mul_nonneg (mul_nonneg hNB (hψ₁.2.1 _)) (hψ₂.2.1 u')) (sq_nonneg _)
  have hgnn : ∀ u : ℝ, 0 ≤ ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 := fun u =>
    mul_nonneg (hψ₂.2.1 u) (sq_nonneg _)
  -- **Fubini**: `∫ R̃² = (∫ ψ₂‖R‖²)(∫ (N B)ψ₁((N B)·))`
  have hFub := prop101_integral_RtildeSq_eq W N B hψ₁ hψ₂
  -- integrability of `R̃²`, through the convolution
  have hIntR : Integrable (fun u : ℝ => RtildeSq W N B ψ₁ ψ₂ u) := by
    rw [prop101_RtildeSq_eq_convolution W N B ψ₁ ψ₂]
    exact MeasureTheory.Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (prop101_integrable_gSq (C₀ := 16) (by norm_num) hψ₂ W)
      (prop101_integrable_scaled_bump hψ₁ ((N : ℝ) * B))
  -- the three steps, with `J = ∫ψ₁`, `G = ∫ ψ₂‖R‖²`
  have step1 : ∫ u, testfun N W B ψ₁ ψ₂ ψ' u ≤ c₃ * ∫ u, RtildeSq W N B ψ₁ ψ₂ u := by
    have hInt2 : Integrable (fun u : ℝ => c₃ * RtildeSq W N B ψ₁ ψ₂ u) := hIntR.const_mul c₃
    have hpt : ∀ u : ℝ, testfun N W B ψ₁ ψ₂ ψ' u ≤ c₃ * RtildeSq W N B ψ₁ ψ₂ u := fun u =>
      mul_le_mul_of_nonneg_right (hψ'acc u) (hRtSqnn u)
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => mul_nonneg (hψ'nn u) (hRtSqnn u)) hInt2
      (Filter.Eventually.of_forall hpt)
    rwa [MeasureTheory.integral_const_mul] at h
  have step2 : ∫ u, RtildeSq W N B ψ₁ ψ₂ u
      ≤ max (∫ x : ℝ, ψ₁ x) 1 * ∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 := by
    have hker := prop101_integral_scaled_bump_le hψ₁ hNB
    have hG0 : 0 ≤ ∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 :=
      integral_nonneg hgnn
    rw [hFub]
    calc (∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2)
            * ∫ t : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * t)
        ≤ (∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) * ∫ x : ℝ, ψ₁ x :=
          mul_le_mul_of_nonneg_left hker hG0
      _ ≤ max (∫ x : ℝ, ψ₁ x) 1 * ∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hG0
  have step3 : ∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 ≤ c₂ * K :=
    (prop101_integral_gSq_le_interval hψ₂le hψ₂.2.1 hψ₂.2.2.1 W).trans
      (mul_le_mul_of_nonneg_left hK hc₂nn)
  -- combine
  have hc₂0 : 0 ≤ c₂ := hc₂nn
  have hJmax0 : 0 ≤ max (∫ x : ℝ, ψ₁ x) 1 := le_trans zero_le_one (le_max_right _ _)
  calc ∫ u, testfun N W B ψ₁ ψ₂ ψ' u
      ≤ c₃ * ∫ u, RtildeSq W N B ψ₁ ψ₂ u := step1
    _ ≤ c₃ * (max (∫ x : ℝ, ψ₁ x) 1 * ∫ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left step2 hc₃nn
    _ ≤ c₃ * (max (∫ x : ℝ, ψ₁ x) 1 * (c₂ * K)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left step3 hJmax0) hc₃nn
    _ = c₃ * max (∫ x : ℝ, ψ₁ x) 1 * c₂ * K := by ring

end

end Work.GM.S3
