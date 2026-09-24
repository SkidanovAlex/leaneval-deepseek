import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Commons.Analysis.Fourier.triangle_kernel_fourier_inversion
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant

/-!
# GM §9: the far-sampling crux

For a nonnegative finitely supported sequence `H : ℤ → ℝ` and `M₃ ≥ 1`, the
`‖ψ̂₁(K M₃ t)‖²`-weighted `L²`-mass of the trigonometric polynomial `t ↦ Σ_ℓ H ℓ e^{2πiℓt}`
outside the window `|t| ≤ 2/M₃` is bounded by a constant times its unweighted mass on the window.

## Strategy

Write `ψ = psi1 K`, `ψc = (ψ : ℝ → ℂ)`, `Ψ = psi1hat K = 𝓕 ψc` (real and even, since `ψ` is),
and `P = ψc ⋆ ψc` (the autocorrelation of `ψ`: real, nonnegative, supported in
`[-(2K+2), 2K+2]`, bounded by `∫ ψ`).

* The Fourier transform of `‖Ψ‖²` is `P`, because
  `𝓕(‖Ψ‖²) = 𝓕(ψc·ψc) = 𝓕ψc ⋆ 𝓕ψc = ψc ⋆ ψc` (Mathlib's convolution theorem
  `Real.fourier_mul_convolution_eq` plus Fourier inversion).
* The Fourier transform of the *tent* `u ↦ tri (u/a)` is `σ ↦ a·sinc(πaσ)² ≥ 0`, which is `≥ a/2`
  for `|σ| ≤ 1/(4a)`.  (Here `Commons.Analysis.Fourier.tri` is the unit tent and
  `integral_tri_cos` computes its cosine transform.)
* The expansion identity `Gsum_expansion` turns an integral against a weight `g` with Fourier
  transform `ĝ` into a *double* sum over pairs of frequencies, weighted by `ĝ((ℓ-ℓ')/M₃)`.

Choosing `a = 1/(8(K+1))`, the autocorrelation `P` vanishes unless `|ℓ-ℓ'| ≤ (2K+2)M₃`, while
the tent transform is `≥ a/2` precisely there; hence the statement with `C = (2/a)·∫ψ = 16(K+1)·∫ψ`.
-/

open MeasureTheory Complex Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine.FarCx

noncomputable section

/-! ## 1. Elementary facts about `psi1` and its Fourier transform -/

/-- `psi1 K` is even. -/
lemma psi1_even (K x : ℝ) : psi1 K (-x) = psi1 K x := by
  rw [psi1, psi1]
  rw [show K + 1 - -x = K + 1 + x by ring, show K + 1 + -x = K + 1 - x by ring, mul_comm]

/-- `psi1 K` has compact support (contained in `[-(K+1), K+1]`). -/
lemma psi1_hasCompactSupport (K : ℝ) : HasCompactSupport (psi1 K) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(K+1)) (K+1)) isCompact_Icc ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Set.mem_Icc]
  have h : ¬ (K + 1 ≤ |x|) := fun h => hx (psi1_eq_zero h)
  rw [not_le, abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

lemma psi1_cont (K : ℝ) : Continuous (psi1 K) := (psi1_contDiff K).continuous

lemma psi1_int (K : ℝ) : Integrable (psi1 K) :=
  (psi1_cont K).integrable_of_hasCompactSupport (psi1_hasCompactSupport K)

/-- `psi1hat K` is even. -/
lemma psi1hat_even (K u : ℝ) : psi1hat K (-u) = psi1hat K u := by
  set f : ℝ → ℂ := fun t => ((psi1 K t : ℝ) : ℂ) with hf
  have hcomp : f ∘ (fun x : ℝ => -x) = f := by funext t; simp [hf, psi1_even]
  have key := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f u
  rw [show (⇑(LinearIsometryEquiv.neg ℝ) : ℝ → ℝ) = fun x => -x from rfl, hcomp] at key
  rw [psi1hat, psi1hat]
  simpa [hf] using key.symm

/-- `psi1hat K` is real-valued. -/
lemma psi1hat_real (K u : ℝ) : (starRingEnd ℂ) (psi1hat K u) = psi1hat K u := by
  have key : (starRingEnd ℂ) (psi1hat K u) = psi1hat K (-u) := by
    simp only [psi1hat, Real.fourier_eq]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Circle.smul_def, smul_eq_mul, map_mul, Complex.conj_ofReal,
      ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, inner_neg_right]
  rw [key, psi1hat_even]

/-- For a real-valued complex number, `‖z‖² = z²`. -/
lemma normSq_eq_sq (z : ℂ) (h : (starRingEnd ℂ) z = z) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, h, sq]

/-- The bump `psi1 K` as a complex-valued function. -/
def psiC (K : ℝ) : ℝ → ℂ := fun x => ((psi1 K x : ℝ) : ℂ)

/-- The autocorrelation `ψc ⋆ ψc` of `psi1 K`. -/
def psiConv (K : ℝ) : ℝ → ℂ := convolution (psiC K) (psiC K) (ContinuousLinearMap.mul ℂ ℂ) volume

/-- The real autocorrelation of `psi1 K`. -/
def psiAuto (K : ℝ) (τ : ℝ) : ℝ := ∫ y, psi1 K y * psi1 K (τ - y)

lemma psiC_cont (K : ℝ) : Continuous (psiC K) :=
  Complex.continuous_ofReal.comp (psi1_cont K)

lemma psiC_cs (K : ℝ) : HasCompactSupport (psiC K) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(K+1)) (K+1)) isCompact_Icc ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Set.mem_Icc]
  have h : ¬ (K + 1 ≤ |x|) := fun h => hx (by simp [psiC, psi1_eq_zero h])
  rw [not_le, abs_lt] at h
  constructor <;> linarith [h.1, h.2]

lemma psiC_int (K : ℝ) : Integrable (psiC K) :=
  (psiC_cont K).integrable_of_hasCompactSupport (psiC_cs K)

lemma psiConv_cont (K : ℝ) : Continuous (psiConv K) :=
  (psiC_cs K).continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
    (psiC_cont K).locallyIntegrable (psiC_cont K)

lemma psiConv_int (K : ℝ) : Integrable (psiConv K) :=
  (psiC_int K).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (psiC_int K)

/-- **The Fourier transform of the convolution** is the product of the Fourier transforms. -/
lemma psiConv_fourier (K : ℝ) : ∀ ξ, 𝓕 (psiConv K) ξ = (psi1hat K ξ) ^ 2 := by
  intro ξ
  rw [psiConv, Real.fourier_mul_convolution_eq (psiC_int K) (psiC_int K) ξ]
  show 𝓕 (psiC K) ξ * 𝓕 (psiC K) ξ = (psi1hat K ξ) ^ 2
  rw [show psi1hat K ξ = 𝓕 (psiC K) ξ from rfl, sq]

lemma psi1hat_cont (K : ℝ) : Continuous (psi1hat K) :=
  VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) (V := ℝ) (W := ℝ) (E := ℂ)
    (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (psiC_int K)

lemma integrable_psi1hat_sq (K : ℝ) (hK : 0 < K) :
    Integrable (fun ξ : ℝ => (psi1hat K ξ) ^ 2) := by
  obtain ⟨C, _hC, hb⟩ := psi1hat_decay K hK 1
  have hbound : ∀ ξ : ℝ, ‖(psi1hat K ξ) ^ 2‖ ≤ C^2 * (1 + ‖ξ‖) ^ (-(2:ℝ)) := by
    intro ξ
    rw [norm_pow]
    have h2 : ‖psi1hat K ξ‖ ≤ C / (1 + |ξ|) := by simpa [Real.norm_eq_abs] using hb ξ
    calc ‖psi1hat K ξ‖ ^ 2 ≤ (C / (1 + |ξ|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = C^2 / (1 + |ξ|) ^ 2 := by rw [div_pow]
      _ = C^2 * (1 + ‖ξ‖) ^ (-(2:ℝ)) := by
          rw [← Real.norm_eq_abs ξ, div_eq_mul_inv, ← Real.rpow_natCast (1 + ‖ξ‖) 2,
            ← Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖)]
          norm_num
  refine Integrable.mono' ?_ ((psi1hat_cont K).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  exact (integrable_one_add_norm (E := ℝ) (by norm_num)).const_mul (C^2)

/-- **The Fourier transform of `‖psi1hat K‖²` is the autocorrelation of `psi1 K`.** -/
lemma Fourier_normSq_psi1hat (K : ℝ) (hK : 0 < K) :
    𝓕 (fun u : ℝ => ((‖psi1hat K u‖ ^ 2 : ℝ) : ℂ)) = psiConv K := by
  have hFint : Integrable (𝓕 (psiConv K)) := by
    rw [show 𝓕 (psiConv K) = fun ξ => (psi1hat K ξ) ^ 2 from funext (psiConv_fourier K)]
    exact integrable_psi1hat_sq K hK
  have hfun : 𝓕⁻ (psiConv K) = fun u : ℝ => ((‖psi1hat K u‖ ^ 2 : ℝ) : ℂ) := by
    funext w
    rw [Real.fourierInv_eq_fourier_neg, psiConv_fourier K (-w), psi1hat_even K w]
    exact (normSq_eq_sq _ (psi1hat_real K w)).symm
  rw [← Continuous.fourier_fourierInv_eq (psiConv_cont K) (psiConv_int K) hFint, hfun]

/-! ## 2. Values of the autocorrelation -/

lemma psiAuto_nonneg (K : ℝ) (τ : ℝ) : 0 ≤ psiAuto K τ :=
  integral_nonneg fun y => mul_nonneg (psi1_nonneg K y) (psi1_nonneg K (τ - y))

lemma psiAuto_int (K : ℝ) (τ : ℝ) :
    Integrable (fun y : ℝ => psi1 K y * psi1 K (τ - y)) := by
  have hcont : Continuous (fun y : ℝ => psi1 K y * psi1 K (τ - y)) :=
    (psi1_cont K).mul ((psi1_cont K).comp (continuous_const.sub continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (τ - (K+1)) (τ + (K+1))) isCompact_Icc ?_
  intro y hy
  rw [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have h2 : |τ - y| ≤ K + 1 := by
    by_contra hc
    exact hy2 (psi1_eq_zero (le_of_not_ge hc))
  rw [Set.mem_Icc]
  rw [abs_le] at h2
  constructor <;> linarith [h2.1, h2.2]

/-- The autocorrelation is bounded by `∫ ψ`. -/
lemma psiConv_apply (K : ℝ) (τ : ℝ) : psiConv K τ = ((psiAuto K τ : ℝ) : ℂ) := by
  have hint := psiAuto_int K τ
  rw [psiAuto]
  change (∫ t : ℝ, psiC K t * psiC K (τ - t))
    = Complex.ofRealCLM ((∫ y : ℝ, psi1 K y * psi1 K (τ - y) : ℝ))
  rw [← Complex.ofRealCLM.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [psiC, Complex.ofRealCLM_apply]
  rw [Complex.ofReal_mul]

lemma psiAuto_le (K : ℝ) (τ : ℝ) : psiAuto K τ ≤ ∫ y, psi1 K y := by
  rw [psiAuto]
  refine integral_mono_ae (psiAuto_int K τ) (psi1_int K)
    (Filter.Eventually.of_forall fun y => ?_)
  exact mul_le_of_le_one_right (psi1_nonneg K y) (psi1_le_one K (τ - y))

/-- The autocorrelation vanishes for `|τ| > 2(K+1)`. -/
lemma psiAuto_eq_zero (K : ℝ) {τ : ℝ} (hτ : 2 * (K + 1) < |τ|) : psiAuto K τ = 0 := by
  rw [psiAuto]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  show psi1 K y * psi1 K (τ - y) = 0
  rcases le_or_gt (K + 1) |y| with h | h
  · rw [psi1_eq_zero h, zero_mul]
  · have h2 : K + 1 ≤ |τ - y| := by
      by_contra hc
      rw [not_le] at hc
      have h3 : |τ| ≤ |τ - y| + |y| := by
        calc |τ| = |(τ - y) + y| := by rw [sub_add_cancel]
          _ ≤ |τ - y| + |y| := abs_add_le _ _
      linarith
    rw [psi1_eq_zero h2, mul_zero]

/-! ## 3. The tent weight and its transform -/

/-- The tent weight of half-width `a`, expressed through `Commons.Analysis.Fourier.tri`. -/
def tentW (a : ℝ) (u : ℝ) : ℝ := Commons.Analysis.Fourier.tri (u / a)

/-- Its cosine/Fourier transform: `a·sinc(πaσ)²`. -/
def tentHat (a : ℝ) (σ : ℝ) : ℝ := a * (Real.sinc (Real.pi * a * σ)) ^ 2

lemma tentW_nonneg (a u : ℝ) : 0 ≤ tentW a u := by
  rw [tentW, Commons.Analysis.Fourier.tri]
  exact le_max_right _ _

lemma tentW_le_one (a u : ℝ) : tentW a u ≤ 1 := by
  rw [tentW, Commons.Analysis.Fourier.tri]
  refine max_le (by linarith [abs_nonneg (u / a)]) zero_le_one

lemma tentW_eq_zero {a u : ℝ} (ha : 0 < a) (h : a ≤ |u|) : tentW a u = 0 := by
  rw [tentW]
  exact Commons.Analysis.Fourier.tri_eq_zero_of_one_le_abs (by
    rw [abs_div, abs_of_pos ha, le_div_iff₀ ha]
    simpa using h)

lemma tentW_even (a : ℝ) : Function.Even (tentW a) := by
  intro u
  rw [tentW, tentW, neg_div]
  exact Commons.Analysis.Fourier.tri_even (u / a)

lemma tentW_int {a : ℝ} (ha : 0 < a) : Integrable (tentW a) := by
  have hcont : Continuous (tentW a) :=
    Commons.Analysis.Fourier.tri_continuous.comp (continuous_id.div_const a)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-a) a) isCompact_Icc ?_
  intro u hu
  rw [Function.mem_support] at hu
  rw [Set.mem_Icc]
  have h : |u| ≤ a := by
    by_contra hc
    rw [not_le] at hc
    exact hu (tentW_eq_zero ha hc.le)
  rw [abs_le] at h
  exact h

/-- The cosine transform of the tent weight: `∫ tri(u/a) cos(2πσu) du = a·sinc(πaσ)²`. -/
lemma tentW_cos (a : ℝ) (ha : 0 < a) (σ : ℝ) :
    ∫ u : ℝ, tentW a u * Real.cos (2 * Real.pi * σ * u) = tentHat a σ := by
  have h1 : (∫ u : ℝ, tentW a u * Real.cos (2 * Real.pi * σ * u))
      = ∫ u : ℝ, Commons.Analysis.Fourier.tri (a⁻¹ * u) *
          Real.cos (2 * Real.pi * (a * σ) * (a⁻¹ * u)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show Commons.Analysis.Fourier.tri (u / a) * Real.cos (2 * Real.pi * σ * u)
      = Commons.Analysis.Fourier.tri (a⁻¹ * u) * Real.cos (2 * Real.pi * (a * σ) * (a⁻¹ * u))
    rw [div_eq_inv_mul]
    congr 1
    field_simp
  rw [h1, MeasureTheory.Measure.integral_comp_inv_mul_left
      (fun v : ℝ => Commons.Analysis.Fourier.tri v * Real.cos (2 * Real.pi * (a * σ) * v)) a,
    abs_of_pos ha, smul_eq_mul, Commons.Analysis.Fourier.integral_tri_cos, tentHat]
  ring_nf

/-- The Fourier-transform identity for the tent weight. -/
lemma tentW_fourier (a : ℝ) (ha : 0 < a) (σ : ℝ) :
    (∫ u : ℝ, (tentW a u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * σ)) * Complex.I))
      = (tentHat a σ : ℂ) := by
  have h := Commons.Analysis.Fourier.integral_mul_exp_eq (tentW_int ha) (tentW_even a) σ
  rw [h, tentW_cos a ha σ]

lemma tentHat_nonneg (a : ℝ) (ha : 0 < a) (σ : ℝ) : 0 ≤ tentHat a σ := by
  rw [tentHat]
  positivity

/-- On `|a σ| ≤ 1/4` the tent transform is at least `a/2`. -/
lemma tentHat_ge (a : ℝ) (ha : 0 < a) {σ : ℝ} (hσ : |a * σ| ≤ 1 / 4) :
    a / 2 ≤ tentHat a σ := by
  rw [tentHat, show Real.pi * a * σ = Real.pi * (a * σ) by ring]
  have h2 := Commons.Analysis.Fourier.sinc_pi_sq_lower_bound hσ
  nlinarith [h2, ha]

/-! ## 4. The expansion identity -/

/-- The exponential sum with frequencies `ℓ/M₃`, in the sign convention of
`fejer_expansion_identity`. -/
def Gsum (s : Finset ℤ) (H : ℤ → ℝ) (M₃ u : ℝ) : ℂ :=
  ∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (ℓ : ℝ) / M₃)) * Complex.I)

/-- Pointwise expansion of `gv * ‖Σ‖²` as a double sum. -/
lemma mul_normSq_Gsum (gv : ℂ) (M₃ u : ℝ) (s : Finset ℤ) (H : ℤ → ℝ) :
    gv * ((‖Gsum s H M₃ u‖ ^ 2 : ℝ) : ℂ)
      = ∑ ℓ ∈ s, ∑ ℓ' ∈ s, (H ℓ : ℂ) * (H ℓ' : ℂ) *
          (gv * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)) := by
  have hnorm : ((‖Gsum s H M₃ u‖ ^ 2 : ℝ) : ℂ)
      = Gsum s H M₃ u * (starRingEnd ℂ) (Gsum s H M₃ u) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have hconj : (starRingEnd ℂ) (Gsum s H M₃ u) = ∑ ℓ' ∈ s,
      (H ℓ' : ℂ) * Complex.exp (↑(2 * Real.pi * u * (ℓ' : ℝ) / M₃) * Complex.I) := by
    rw [Gsum, map_sum]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
  rw [hnorm, hconj, Gsum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  have hexp : ↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I
      = ↑(-(2 * Real.pi * u * (ℓ : ℝ) / M₃)) * Complex.I
        + ↑(2 * Real.pi * u * (ℓ' : ℝ) / M₃) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]
  push_cast
  ring_nf

/-- `Gsum` is continuous. -/
lemma Gsum_cont (s : Finset ℤ) (H : ℤ → ℝ) (M₃ : ℝ) : Continuous (Gsum s H M₃) := by
  show Continuous (fun u : ℝ => ∑ ℓ ∈ s,
    (H ℓ : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (ℓ : ℝ) / M₃)) * Complex.I))
  fun_prop

/-- `g u * ‖Gsum‖²` is integrable whenever `g` is (the second factor is bounded). -/
lemma integrable_mul_Gsum_normSq {g : ℝ → ℝ} (hg : Integrable g) (M₃ : ℝ) (s : Finset ℤ)
    (H : ℤ → ℝ) : Integrable (fun u : ℝ => g u * ‖Gsum s H M₃ u‖ ^ 2) := by
  have hbdd : ∀ u : ℝ, ‖Gsum s H M₃ u‖ ≤ ∑ ℓ ∈ s, ‖H ℓ‖ := by
    intro u
    rw [Gsum]
    calc ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (ℓ : ℝ) / M₃)) * Complex.I)‖
        ≤ ∑ ℓ ∈ s, ‖(H ℓ : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (ℓ : ℝ) / M₃)) * Complex.I)‖ :=
          norm_sum_le _ _
      _ = ∑ ℓ ∈ s, ‖H ℓ‖ := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
            show ‖((H ℓ : ℝ) : ℂ)‖ = ‖H ℓ‖ from Complex.norm_real (H ℓ)]
  have hInt : Integrable (fun u : ℝ => |g u| * (∑ ℓ ∈ s, ‖H ℓ‖) ^ 2) := hg.abs.mul_const _
  refine hInt.mono' (hg.1.mul (((Gsum_cont s H M₃).norm).pow 2).aestronglyMeasurable) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Gsum s H M₃ u‖)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbdd u) 2) (abs_nonneg _)

lemma Gsum_expansion {g : ℝ → ℝ} (hg : Integrable g) {ĝ : ℝ → ℝ}
    (hĜ : ∀ σ : ℝ,
      (∫ u : ℝ, (g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * σ)) * Complex.I)) = (ĝ σ : ℂ))
    (M₃ : ℝ) (s : Finset ℤ) (H : ℤ → ℝ) :
    (∫ u : ℝ, g u * ‖Gsum s H M₃ u‖ ^ 2)
      = ∑ ℓ ∈ s, ∑ ℓ' ∈ s, H ℓ * H ℓ' * ĝ (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃) := by
  set F : ℝ → ℂ := fun u => ∑ ℓ ∈ s, ∑ ℓ' ∈ s, (H ℓ : ℂ) * (H ℓ' : ℂ) *
      ((g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I))
    with hFdef
  have hphase : ∀ ℓ ℓ' : ℤ, Continuous (fun u : ℝ =>
      Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)) := by
    intro ℓ ℓ'
    exact Complex.continuous_exp.comp (by fun_prop)
  have hsummand_int : ∀ ℓ ℓ' : ℤ,
      Integrable (fun u : ℝ => (H ℓ : ℂ) * (H ℓ' : ℂ) *
        ((g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I))) := by
    intro ℓ ℓ'
    have h1 : Integrable (fun u : ℝ => (g u : ℂ) *
        Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)) :=
      hg.ofReal.mul_bdd (hphase ℓ ℓ').aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by rw [Complex.norm_exp_ofReal_mul_I])
    exact (h1.const_mul ((H ℓ : ℂ) * (H ℓ' : ℂ))).congr
      (Filter.Eventually.of_forall fun u => by simp only [Pi.smul_apply, smul_eq_mul])
  have hFint : Integrable F := by
    rw [hFdef]
    exact Commons.Analysis.Fourier.integrable_finset_sum s fun ℓ _ =>
      Commons.Analysis.Fourier.integrable_finset_sum s fun ℓ' _ => hsummand_int ℓ ℓ'
  have hpoint : ∀ u : ℝ, ((g u * ‖Gsum s H M₃ u‖ ^ 2 : ℝ) : ℂ) = F u := by
    intro u
    rw [Complex.ofReal_mul, mul_normSq_Gsum, hFdef]
  have hcomp : (∫ u : ℝ, ((g u * ‖Gsum s H M₃ u‖ ^ 2 : ℝ) : ℂ)) = ∫ u : ℝ, F u :=
    integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have h1 : ((∫ u : ℝ, g u * ‖Gsum s H M₃ u‖ ^ 2 : ℝ) : ℂ)
      = ∫ u : ℝ, ((g u * ‖Gsum s H M₃ u‖ ^ 2 : ℝ) : ℂ) := by
    have h := Complex.ofRealCLM.integral_comp_comm
      (φ := fun u : ℝ => g u * ‖Gsum s H M₃ u‖ ^ 2) (integrable_mul_Gsum_normSq hg M₃ s H)
    simpa only [Complex.ofRealCLM_apply] using h.symm
  have hC : (∫ u : ℝ, F u)
      = (((∑ ℓ ∈ s, ∑ ℓ' ∈ s, H ℓ * H ℓ' * ĝ (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)) : ℝ) : ℂ) := by
    rw [hFdef]
    have h1' : (∫ u : ℝ, ∑ ℓ ∈ s, ∑ ℓ' ∈ s, (H ℓ : ℂ) * (H ℓ' : ℂ) *
        ((g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)))
        = ∑ ℓ ∈ s, ∫ u : ℝ, ∑ ℓ' ∈ s, (H ℓ : ℂ) * (H ℓ' : ℂ) *
        ((g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)) :=
      integral_finsetSum s (fun ℓ _ => Commons.Analysis.Fourier.integrable_finset_sum s
        fun ℓ' _ => hsummand_int ℓ ℓ')
    rw [h1']
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have h2' : (∫ u : ℝ, ∑ ℓ' ∈ s, (H ℓ : ℂ) * (H ℓ' : ℂ) *
        ((g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)))
        = ∑ ℓ' ∈ s, ∫ u : ℝ, (H ℓ : ℂ) * (H ℓ' : ℂ) *
        ((g u : ℂ) * Complex.exp (↑(-(2 * Real.pi * u * (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃))) * Complex.I)) :=
      integral_finsetSum s (fun ℓ' _ => hsummand_int ℓ ℓ')
    rw [h2', Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_mul, integral_const_mul, hĜ]
  exact Complex.ofReal_injective (by rw [h1, hcomp, hC])

/-- For a real-valued complex number, the real part of its square is the squared norm. -/
lemma re_sq_eq_normSq (z : ℂ) (h : (starRingEnd ℂ) z = z) : (z ^ 2).re = ‖z‖ ^ 2 := by
  rw [← normSq_eq_sq z h, Complex.ofReal_re]

/-! ## 5. The crux -/

/-- **The weighted far mass is bounded by the window mass.**  For `M₃ ≥ 1`, a nonnegative
finitely supported `H` and the weight `‖psi1hat K‖²`, the mass of the exponential sum outside
`|u| ≤ 2` is at most a constant times its mass inside. -/
theorem crux_bound {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ M₃ : ℝ, 1 ≤ M₃ → ∀ (s : Finset ℤ) (H : ℤ → ℝ), (∀ ℓ, 0 ≤ H ℓ) →
      ((∫ u in Set.Ioi 2, ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
        + ∫ u in Set.Iio (-2), ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
      ≤ C * ∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2 := by
  have hK1 : (0:ℝ) < K + 1 := by linarith
  set Q : ℝ := ∫ y, psi1 K y with hQdef
  have hQnn : 0 ≤ Q := by
    rw [hQdef]; exact integral_nonneg (psi1_nonneg K)
  refine ⟨16 * (K + 1) * Q + 1, by positivity, ?_⟩
  intro M₃ hM₃ s H hH
  set a : ℝ := 1 / (8 * (K + 1)) with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  set W : ℝ → ℝ := fun u => ‖psi1hat K u‖ ^ 2 with hWdef
  have hWeq : ∀ u, W u = ‖psi1hat K u‖ ^ 2 := fun u => rfl
  have hWint : Integrable W := by
    refine ((integrable_psi1hat_sq K hK).re).congr (Filter.Eventually.of_forall fun u => ?_)
    show ((psi1hat K u) ^ 2).re = W u
    rw [hWdef]
    exact re_sq_eq_normSq _ (psi1hat_real K u)
  -- expansion with the weight `W`, whose transform is the autocorrelation
  have hexpW : (∫ u : ℝ, W u * ‖Gsum s H M₃ u‖ ^ 2)
      = ∑ ℓ ∈ s, ∑ ℓ' ∈ s, H ℓ * H ℓ' * psiAuto K (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃) := by
    refine Gsum_expansion hWint ?_ M₃ s H
    intro σ
    have h := congrFun (Fourier_normSq_psi1hat K hK) σ
    rw [Real.fourier_real_eq_integral_exp_smul, psiConv_apply K σ] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul, hWdef]
    ring
  -- expansion with the tent weight, whose transform is `tentHat a`
  have hexpT : (∫ u : ℝ, tentW a u * ‖Gsum s H M₃ u‖ ^ 2)
      = ∑ ℓ ∈ s, ∑ ℓ' ∈ s, H ℓ * H ℓ' * tentHat a (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃) :=
    Gsum_expansion (tentW_int ha) (tentW_fourier a ha) M₃ s H
  -- the restricted pair sum
  set R : ℝ := ∑ ℓ ∈ s, ∑ ℓ' ∈ s,
    (if |(((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)| ≤ 2 * (K + 1) then H ℓ * H ℓ' else 0) with hRdef
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    refine Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun ℓ' _ => ?_
    by_cases h : |(((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)| ≤ 2 * (K + 1)
    · rw [if_pos h]; exact mul_nonneg (hH ℓ) (hH ℓ')
    · rw [if_neg h]
  -- upper bound: the far mass is at most `Q * R`
  have hfW : Integrable (fun u : ℝ => ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2) := by
    refine (integrable_mul_Gsum_normSq hWint M₃ s H).congr
      (Filter.Eventually.of_forall fun u => ?_)
    show W u * ‖Gsum s H M₃ u‖ ^ 2 = ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2
    rw [hWdef]; ring
  have hfar_le : (∫ u in Set.Ioi 2, ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
        + ∫ u in Set.Iio (-2), ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2
      ≤ Q * R := by
    have hnn : 0 ≤ᵐ[volume] fun u : ℝ => ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2 :=
      Filter.Eventually.of_forall fun u => by positivity
    have h1 : (∫ u in Set.Ioi 2, ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
        + ∫ u in Set.Iio (-2), ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2
        ≤ ∫ u : ℝ, ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2 := by
      rw [← setIntegral_union (s := Set.Ioi 2) (t := Set.Iio (-2))
        (Set.disjoint_left.mpr (fun x hx hx' => by simp at hx hx'; linarith))
        measurableSet_Iio hfW.integrableOn hfW.integrableOn]
      exact setIntegral_le_integral (s := Set.Ioi 2 ∪ Set.Iio (-2)) hfW hnn
    have h2 := h1
    have h3 : (∫ u : ℝ, ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2) ≤ Q * R := by
      rw [show (∫ u : ℝ, ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2)
          = ∫ u : ℝ, W u * ‖Gsum s H M₃ u‖ ^ 2 from
        integral_congr_ae (Filter.Eventually.of_forall fun u => by
          show ‖Gsum s H M₃ u‖ ^ 2 * ‖psi1hat K u‖ ^ 2 = W u * ‖Gsum s H M₃ u‖ ^ 2
          rw [hWdef]; ring)]
      rw [hexpW]
      calc ∑ ℓ ∈ s, ∑ ℓ' ∈ s, H ℓ * H ℓ' * psiAuto K (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)
            ≤ ∑ ℓ ∈ s, ∑ ℓ' ∈ s,
                (if |(((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)| ≤ 2 * (K + 1) then Q * (H ℓ * H ℓ') else 0) := by
              refine Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun ℓ' _ => ?_
              have hτ := psiAuto_le K (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)
              by_cases h : |(((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)| ≤ 2 * (K + 1)
              · rw [if_pos h]
                calc H ℓ * H ℓ' * psiAuto K (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)
                    ≤ H ℓ * H ℓ' * Q :=
                      mul_le_mul_of_nonneg_left hτ (mul_nonneg (hH ℓ) (hH ℓ'))
                  _ = Q * (H ℓ * H ℓ') := by ring
              · rw [if_neg h]
                rw [psiAuto_eq_zero K (by
                  rw [not_le] at h
                  linarith), mul_zero]
          _ = Q * R := by
              rw [hRdef, Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ' _ => ?_
              by_cases h : |(((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)| ≤ 2 * (K + 1)
              · simp only [if_pos h]
              · simp only [if_neg h, mul_zero]
    exact le_trans h1 h3
  -- lower bound: the window mass is at least `(a/2) * R`
  have hwin_ge : (a / 2) * R ≤ ∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2 := by
    have hsupp : ∀ u : ℝ, tentW a u * ‖Gsum s H M₃ u‖ ^ 2
        = (Set.Icc (-2) 2).indicator (fun u => tentW a u * ‖Gsum s H M₃ u‖ ^ 2) u := by
      intro u
      by_cases hu : u ∈ Set.Icc (-2) 2
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu]
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
        have ha2 : a ≤ 2 := by
          rw [hadef, div_le_iff₀ (by positivity)]; nlinarith [hK1]
        rcases hu with h | h
        · have hle : a ≤ |u| := by rw [abs_of_neg (by linarith)]; linarith
          rw [tentW_eq_zero ha hle, zero_mul]
        · have hle : a ≤ |u| := by rw [abs_of_pos (by linarith)]; linarith
          rw [tentW_eq_zero ha hle, zero_mul]
    have h1 : (∫ u : ℝ, tentW a u * ‖Gsum s H M₃ u‖ ^ 2)
        = ∫ u in Set.Icc (-2) 2, tentW a u * ‖Gsum s H M₃ u‖ ^ 2 := by
      rw [show (∫ u : ℝ, tentW a u * ‖Gsum s H M₃ u‖ ^ 2)
          = ∫ u : ℝ, (Set.Icc (-2) 2).indicator (fun u => tentW a u * ‖Gsum s H M₃ u‖ ^ 2) u
          from integral_congr_ae (Filter.Eventually.of_forall hsupp)]
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    have h2 : (∫ u in Set.Icc (-2) 2, tentW a u * ‖Gsum s H M₃ u‖ ^ 2)
        ≤ ∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2 := by
      refine setIntegral_mono_on ?_ ?_ measurableSet_Icc ?_
      · exact (integrable_mul_Gsum_normSq (tentW_int ha) M₃ s H).integrableOn
      · exact ((Gsum_cont s H M₃).norm.pow 2).integrableOn_Icc
      · intro u _
        calc tentW a u * ‖Gsum s H M₃ u‖ ^ 2 ≤ 1 * ‖Gsum s H M₃ u‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (tentW_le_one a u) (by positivity)
          _ = ‖Gsum s H M₃ u‖ ^ 2 := by ring
    have h3 : (a / 2) * R ≤ ∫ u : ℝ, tentW a u * ‖Gsum s H M₃ u‖ ^ 2 := by
      rw [hexpT]
      rw [hRdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ℓ' _ => ?_
      by_cases h : |(((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)| ≤ 2 * (K + 1)
      · rw [if_pos h]
        have hge : a / 2 ≤ tentHat a (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃) := by
          refine tentHat_ge a ha ?_
          rw [abs_mul, abs_of_pos ha, hadef]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [h, hK1]
        calc (a / 2) * (H ℓ * H ℓ') ≤ (H ℓ * H ℓ') * tentHat a (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃) := by
              rw [mul_comm (a / 2)]
              exact mul_le_mul_of_nonneg_left hge (mul_nonneg (hH ℓ) (hH ℓ'))
          _ = H ℓ * H ℓ' * tentHat a (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃) := by ring
      · rw [if_neg h]
        have h1 : (0:ℝ) ≤ H ℓ * H ℓ' := mul_nonneg (hH ℓ) (hH ℓ')
        have h2 := tentHat_nonneg a ha (((ℓ : ℝ) - (ℓ' : ℝ)) / M₃)
        nlinarith [mul_nonneg h1 h2]
    linarith [h1, h2]
  -- combine
  have hconst : 2 / a = 16 * (K + 1) := by
    rw [hadef]; field_simp; ring
  have hstep : Q * R ≤ (16 * (K + 1) * Q + 1) * (∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2) := by
    have ha2 : 0 < a / 2 := by positivity
    have hRle : R ≤ (2 / a) * (∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2) := by
      have h2 := mul_le_mul_of_nonneg_left hwin_ge (by positivity : (0:ℝ) ≤ 2 / a)
      have h3 : 2 / a * (a / 2 * R) = R := by field_simp
      rwa [show 2 / a * (a / 2 * R) = R from h3] at h2
    calc Q * R ≤ Q * ((2 / a) * ∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hRle hQnn
      _ = 16 * (K + 1) * Q * (∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2) := by
          rw [hconst]; ring
      _ ≤ (16 * (K + 1) * Q + 1) * (∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun u => by positivity)
          linarith
  have hnn2 : 0 ≤ ∫ u in Set.Icc (-2) 2, ‖Gsum s H M₃ u‖ ^ 2 :=
    integral_nonneg fun u => by positivity
  exact le_trans hfar_le hstep


end

end Work.GM.Affine.FarCx
