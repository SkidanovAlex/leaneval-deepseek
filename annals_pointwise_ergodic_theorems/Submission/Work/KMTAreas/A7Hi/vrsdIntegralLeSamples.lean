import Mathlib
import Submission.Work.KMTAreas.A7Hi.integral_le_latticeVrSampling
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Work.KMTAreas.A7Rep.SamplingKernelDefs

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-! ## The Fourier transform of the sampling kernel -/

/-- The Fourier transform of the sampling kernel `samplingKernel = 𝓕⁻ samplingChi` is the sampling
cutoff `samplingChi` itself. -/
lemma fourier_samplingKernel :
    FourierTransform.fourier (Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ)
      = fun ξ : ℝ => (Work.KMTAreas.A7Rep.samplingChi : ℝ → ℂ) ξ := by
  rw [Work.KMTAreas.A7Rep.samplingKernel_coe]
  exact Work.KMTAreas.A7Rep.samplingChi.continuous.fourier_fourierInv_eq
    Work.KMTAreas.A7Rep.samplingChi.integrable (by
      simpa only [SchwartzMap.fourier_coe] using
        (𝓕 Work.KMTAreas.A7Rep.samplingChi).integrable)

/-! ## A Fourier substitution for the Schwartz factor -/

/-- The Fourier transform of `t ↦ ψ (u - t)` at the frequency `c`:
`∫ t, ψ (u - t) · e^{2πi c t} dt = e^{2πi c u} · 𝓕ψ c`. -/
lemma integral_psi_sub_mul_exp (ψ : SchwartzMap ℝ ℂ) (u c : ℝ) :
    (∫ t : ℝ, (ψ : ℝ → ℂ) (u - t) * Complex.exp (↑(2 * Real.pi * c * t) * Complex.I))
      = Complex.exp (↑(2 * Real.pi * c * u) * Complex.I) *
          FourierTransform.fourier (ψ : ℝ → ℂ) c := by
  set G : ℝ → ℂ := fun s => (ψ : ℝ → ℂ) s *
      Complex.exp (↑(2 * Real.pi * c * (u - s)) * Complex.I) with hG
  have hpt : (fun t : ℝ => (ψ : ℝ → ℂ) (u - t) *
        Complex.exp (↑(2 * Real.pi * c * t) * Complex.I)) = fun t : ℝ => G (u - t) := by
    funext t
    simp only [hG]
    congr 1
    ring_nf
  have hred : (∫ t : ℝ, G (u - t)) = ∫ s : ℝ, G s :=
    MeasureTheory.integral_sub_left_eq_self G volume u
  rw [hpt, hred]
  have hsplit : G = fun s : ℝ => Complex.exp (↑(2 * Real.pi * c * u) * Complex.I) *
      (Complex.exp (↑(-2 * Real.pi * c * s) * Complex.I) * (ψ : ℝ → ℂ) s) := by
    funext s
    simp only [hG]
    rw [show Complex.exp (↑(2 * Real.pi * c * (u - s)) * Complex.I)
        = Complex.exp (↑(2 * Real.pi * c * u) * Complex.I) *
          Complex.exp (↑(-2 * Real.pi * c * s) * Complex.I) by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring]
    ring_nf
  rw [hsplit, integral_const_mul]
  congr 1
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with s
  rw [Real.inner_apply, smul_eq_mul]
  push_cast
  ring_nf

/-! ## The lattice reproducing formula in amplitude form

If `W` is integrable and supported in `[-c,c]` with `c < 1/2`, and `ψ` is a Schwartz function whose
Fourier transform is `1` on `[-c,c]` and `0` outside `[-1/2,1/2]`, then the band-limited function
`𝓕⁻ W` is reproduced from its integer-lattice samples by `ψ`:

  `∀ u, 𝓕⁻ W u = ∑'_m ψ (u - m) · 𝓕⁻ W m`.

This is `Commons.Analysis.Fourier.sampling_reproducing` with the hypothesis that `𝓕⁻ W` itself is
integrable removed: the proof is Poisson summation applied to `t ↦ ψ (u - t) · 𝓕⁻ W t`, whose
Fourier transform is computed by a Fubini on the amplitude side. -/
theorem fourierInv_lattice_reproduction (W : ℝ → ℂ) (hW : MeasureTheory.Integrable W)
    {c : ℝ} (hc : c < 1 / 2)
    (hband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-c) c → W ξ = 0)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ1 : ∀ ξ ∈ Set.Icc (-c) c, FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 1)
    (hψs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) →
      FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 0) :
    ∀ u : ℝ, FourierTransformInv.fourierInv W u
      = ∑' m : ℤ, (ψ : ℝ → ℂ) (u - (m : ℝ)) *
          FourierTransformInv.fourierInv W (m : ℝ) := by
  intro u
  have hf_cont : Continuous (FourierTransformInv.fourierInv W) := by
    have h1 : (⇑(Real.Lp.fourierTransformInv
        (MemLp.toLp W (memLp_one_iff_integrable.mpr hW))) : ℝ → ℂ)
        = FourierTransformInv.fourierInv W := Real.Lp.fourierTransformInv_toLp _
    rw [← h1]
    exact (Real.Lp.fourierTransformInv _).continuous
  set Bw : ℝ := ∫ η : ℝ, ‖W η‖ with hBw
  have hBwnn : 0 ≤ Bw := integral_nonneg (fun η => norm_nonneg _)
  have hf_bdd : ∀ t : ℝ, ‖FourierTransformInv.fourierInv W t‖ ≤ Bw := by
    intro t
    rw [Real.fourierInv_eq']
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [hBw]
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.inner_apply, smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  obtain ⟨Ck, hCkpos, hCkdec⟩ := Commons.Analysis.Fourier.schwartzMap_decay_one_add_sq ψ
  set hF : ℝ → ℂ := fun t => (ψ : ℝ → ℂ) (u - t) * FourierTransformInv.fourierInv W t with hFdef
  have hFcont : Continuous hF :=
    ((ψ.continuous.comp (continuous_const.sub continuous_id)).mul hf_cont)
  have hFbound : ∀ t : ℝ, max 2 (2 * |u| + 2) ≤ |t| →
      ‖hF t‖ ≤ (4 * Bw * Ck) * |t| ^ (-(2 : ℝ)) := by
    intro t ht
    have h1 : 2 * |u| + 2 ≤ |t| := le_trans (le_max_right _ _) ht
    have h2 : (2 : ℝ) ≤ |t| := le_trans (le_max_left _ _) ht
    have htpos : 0 < |t| := by linarith
    have hut : |t| / 2 ≤ |u - t| := by
      have h0 : |u| ≤ |t| / 2 - 1 := by linarith
      have htri : |t| ≤ |u| + |u - t| := by
        calc |t| = |u + (t - u)| := by ring_nf
          _ ≤ |u| + |t - u| := abs_add_le _ _
          _ = |u| + |u - t| := by rw [abs_sub_comm]
      linarith
    have hsq : t ^ 2 / 4 ≤ (u - t) ^ 2 := by
      have hh : (|t| / 2) ^ 2 ≤ |u - t| ^ 2 := by
        nlinarith [hut, abs_nonneg t, abs_nonneg (u - t)]
      rw [div_pow, sq_abs, sq_abs] at hh
      norm_num at hh
      linarith [hh]
    have ht2 : 0 < t ^ 2 := by nlinarith [h2, sq_abs t, abs_nonneg t]
    have hle : 1 / (1 + (u - t) ^ 2) ≤ 4 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) ht2]
      nlinarith [hsq, sq_nonneg (u - t)]
    have hCle : ‖(ψ : ℝ → ℂ) (u - t)‖ ≤ Ck * (4 / t ^ 2) := by
      calc ‖(ψ : ℝ → ℂ) (u - t)‖ ≤ Ck / (1 + (u - t) ^ 2) := hCkdec (u - t)
        _ = Ck * (1 / (1 + (u - t) ^ 2)) := by rw [div_eq_mul_one_div]
        _ ≤ Ck * (4 / t ^ 2) := mul_le_mul_of_nonneg_left hle hCkpos.le
    have h1r : |t| ^ (-(2 : ℝ)) = 1 / t ^ 2 := by
      rw [Real.rpow_neg (abs_nonneg t), Real.rpow_two, one_div, sq_abs]
    rw [h1r, hFdef, norm_mul]
    calc ‖(ψ : ℝ → ℂ) (u - t)‖ * ‖FourierTransformInv.fourierInv W t‖
          ≤ (Ck * (4 / t ^ 2)) * Bw :=
          mul_le_mul hCle (hf_bdd t) (norm_nonneg _) (by positivity)
      _ = 4 * Bw * Ck * (1 / t ^ 2) := by ring
  have hnn : (0 : ℝ) ≤ 4 * Bw * Ck := mul_nonneg (mul_nonneg (by norm_num) hBwnn) hCkpos.le
  have hFdecayTop : hF =O[Filter.atTop] (fun t : ℝ => |t| ^ (-(2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound (4 * Bw * Ck) ?_
    rw [Filter.eventually_atTop]
    refine ⟨max 2 (2 * |u| + 2), fun t ht => ?_⟩
    have ht' : max 2 (2 * |u| + 2) ≤ |t| := by
      have hmax : (2 : ℝ) ≤ max 2 (2 * |u| + 2) := le_max_left _ _
      have ht0 : 0 ≤ t := by linarith
      calc max 2 (2 * |u| + 2) ≤ t := ht
        _ = |t| := (abs_of_nonneg ht0).symm
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    exact hFbound t ht'
  have hFdecayBot : hF =O[Filter.atBot] (fun t : ℝ => |t| ^ (-(2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound (4 * Bw * Ck) ?_
    rw [Filter.eventually_atBot]
    refine ⟨-(max 2 (2 * |u| + 2)), fun t ht => ?_⟩
    have ht' : max 2 (2 * |u| + 2) ≤ |t| := by
      have hmax : (2 : ℝ) ≤ max 2 (2 * |u| + 2) := le_max_left _ _
      have ht0 : t ≤ 0 := by linarith
      calc max 2 (2 * |u| + 2) ≤ -t := by linarith
        _ = |t| := (abs_of_nonpos ht0).symm
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    exact hFbound t ht'
  have hFdecay : hF =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(2 : ℝ))) := by
    rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
    exact ⟨hFdecayBot, hFdecayTop⟩
  have hexp : ∀ t : ℝ, FourierTransformInv.fourierInv W t
      = ∫ η : ℝ, Complex.exp (↑(2 * Real.pi * η * t) * Complex.I) * W η := by
    intro t
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.inner_apply, smul_eq_mul]
    push_cast
    ring
  have hFhat : ∀ k : ℤ, FourierTransform.fourier hF (k : ℝ)
      = ∫ η : ℝ, W η * (FourierTransform.fourier (ψ : ℝ → ℂ) (η - (k : ℝ)) *
          Complex.exp (↑(2 * Real.pi * (η - (k : ℝ)) * u) * Complex.I)) := by
    intro k
    set Fp : ℝ × ℝ → ℂ := fun p => (Complex.exp (↑(-2 * Real.pi * (p.1 * (k : ℝ))) * Complex.I) *
        ((ψ : ℝ → ℂ) (u - p.1) * Complex.exp (↑(2 * Real.pi * p.2 * p.1) * Complex.I))) *
          W p.2 with hFp
    have hFhat_k : FourierTransform.fourier hF (k : ℝ)
        = ∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * (t * (k : ℝ))) * Complex.I) * hF t := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.inner_apply, smul_eq_mul]
    have hint : Integrable (Function.uncurry (fun t η : ℝ => Fp (t, η))) (volume.prod volume) := by
      set A : ℝ × ℝ → ℂ := fun p => Complex.exp (↑(-2 * Real.pi * (p.1 * (k : ℝ))) * Complex.I) *
          ((ψ : ℝ → ℂ) (u - p.1) *
            Complex.exp (↑(2 * Real.pi * p.2 * p.1) * Complex.I)) with hA
      have hAcont : Continuous A := by rw [hA]; fun_prop
      refine Integrable.mono' (Integrable.mul_prod
        ((ψ.integrable.norm).comp_sub_left u) hW.norm) ?_ ?_
      · refine AEStronglyMeasurable.congr
          ((hAcont.aestronglyMeasurable).mul (hW.aestronglyMeasurable.comp_snd)) ?_
        filter_upwards with p
        simp only [Pi.mul_apply, Function.uncurry, hFp, hA]
      · filter_upwards with p
        simp only [Function.uncurry, hFp, norm_mul, Complex.norm_exp_ofReal_mul_I,
          one_mul, mul_one]
        exact le_refl _
    calc FourierTransform.fourier hF (k : ℝ)
        = ∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * (t * (k : ℝ))) * Complex.I) * hF t := hFhat_k
      _ = ∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * (t * (k : ℝ))) * Complex.I) *
            ((ψ : ℝ → ℂ) (u - t) *
              (∫ η : ℝ, Complex.exp (↑(2 * Real.pi * η * t) * Complex.I) * W η)) := by
          apply integral_congr_ae
          filter_upwards with t
          simp only [hFdef, hexp t]
      _ = ∫ t : ℝ, ∫ η : ℝ, Fp (t, η) := by
          apply integral_congr_ae
          filter_upwards with t
          rw [← integral_const_mul, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with η
          simp only [hFp]
          ring
      _ = ∫ η : ℝ, ∫ t : ℝ, Fp (t, η) :=
          integral_integral_swap (f := fun t η : ℝ => Fp (t, η)) hint
      _ = ∫ η : ℝ, W η * (∫ t : ℝ, (ψ : ℝ → ℂ) (u - t) *
            Complex.exp (↑(2 * Real.pi * (η - (k : ℝ)) * t) * Complex.I)) := by
          apply integral_congr_ae
          filter_upwards with η
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with t
          have hAB : Complex.exp (↑(-2 * Real.pi * (t * (k : ℝ))) * Complex.I) *
                Complex.exp (↑(2 * Real.pi * η * t) * Complex.I)
              = Complex.exp (↑(2 * Real.pi * (η - (k : ℝ)) * t) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [show Fp (t, η) = (Complex.exp (↑(-2 * Real.pi * (t * (k : ℝ))) * Complex.I) *
                Complex.exp (↑(2 * Real.pi * η * t) * Complex.I)) *
                  ((ψ : ℝ → ℂ) (u - t) * W η) by
              simp only [hFp]
              ring,
            hAB]
          ring
      _ = ∫ η : ℝ, W η * (FourierTransform.fourier (ψ : ℝ → ℂ) (η - (k : ℝ)) *
            Complex.exp (↑(2 * Real.pi * (η - (k : ℝ)) * u) * Complex.I)) := by
          apply integral_congr_ae
          filter_upwards with η
          rw [integral_psi_sub_mul_exp ψ u (η - (k : ℝ))]
          ring
  have hFhat_zero : ∀ k : ℤ, k ≠ 0 → FourierTransform.fourier hF (k : ℝ) = 0 := by
    intro k hk
    have hzero : ∀ η : ℝ, W η * (FourierTransform.fourier (ψ : ℝ → ℂ) (η - (k : ℝ)) *
        Complex.exp (↑(2 * Real.pi * (η - (k : ℝ)) * u) * Complex.I)) = 0 := by
      intro η
      by_cases hψk : FourierTransform.fourier (ψ : ℝ → ℂ) (η - (k : ℝ)) = 0
      · rw [hψk, zero_mul, mul_zero]
      · have hW0 : W η = 0 := by
          by_contra hWne
          have hmem1 : η ∈ Set.Icc (-c) c := by
            by_contra hcon
            exact hWne (hband η hcon)
          have hmem2 : η - (k : ℝ) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
            by_contra hcon
            exact hψk (hψs _ hcon)
          have h1 : |(k : ℝ)| ≤ c + 1 / 2 := by
            calc |(k : ℝ)| = |η - (η - (k : ℝ))| := by ring_nf
              _ ≤ |η - 0| + |0 - (η - (k : ℝ))| := abs_sub_le η 0 (η - (k : ℝ))
              _ = |η| + |η - (k : ℝ)| := by rw [sub_zero, zero_sub, abs_neg]
              _ ≤ c + 1 / 2 := add_le_add (abs_le.mpr hmem1) (abs_le.mpr hmem2)
          have h2 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
          linarith
        rw [hW0, zero_mul]
    calc FourierTransform.fourier hF (k : ℝ)
        = ∫ η : ℝ, W η * (FourierTransform.fourier (ψ : ℝ → ℂ) (η - (k : ℝ)) *
            Complex.exp (↑(2 * Real.pi * (η - (k : ℝ)) * u) * Complex.I)) := hFhat k
      _ = 0 := by
          simp only [hzero]
          simp
  have hFhat_zero0 : FourierTransform.fourier hF 0 = FourierTransformInv.fourierInv W u := by
    rw [show (0 : ℝ) = (((0 : ℤ)) : ℝ) by norm_num, hFhat 0]
    simp only [Int.cast_zero, sub_zero]
    rw [show (∫ η : ℝ, W η * (FourierTransform.fourier (ψ : ℝ → ℂ) η *
          Complex.exp (↑(2 * Real.pi * η * u) * Complex.I)))
        = ∫ η : ℝ, W η * Complex.exp (↑(2 * Real.pi * η * u) * Complex.I) by
      apply integral_congr_ae
      filter_upwards with η
      by_cases h : W η = 0
      · rw [h, zero_mul, zero_mul]
      · have hmem : η ∈ Set.Icc (-c) c := by
          by_contra hcon
          exact h (hband η hcon)
        rw [hψ1 η hmem, one_mul]]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.inner_apply, smul_eq_mul]
    push_cast
    ring
  have hsum : Summable (fun n : ℤ => FourierTransform.fourier hF (n : ℝ)) :=
    summable_of_ne_finset_zero (s := {0}) (fun b hb => hFhat_zero b (by simpa using hb))
  have hRHS : (∑' n : ℤ, FourierTransform.fourier hF (n : ℝ) *
        (fourier n) ((0 : ℝ) : UnitAddCircle)) = FourierTransform.fourier hF 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro b hb
      rw [hFhat_zero b hb, zero_mul]
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hFcont one_lt_two hFdecay
    hsum 0
  calc FourierTransformInv.fourierInv W u
      = FourierTransform.fourier hF 0 := hFhat_zero0.symm
    _ = ∑' n : ℤ, FourierTransform.fourier hF (n : ℝ) *
          (fourier n) ((0 : ℝ) : UnitAddCircle) := hRHS.symm
    _ = ∑' n : ℤ, hF (0 + (n : ℝ)) := hpois.symm
    _ = ∑' n : ℤ, (ψ : ℝ → ℂ) (u - (n : ℝ)) *
          FourierTransformInv.fourierInv W (n : ℝ) := by
        apply tsum_congr
        intro n
        simp only [zero_add, hFdef]

/-! ## Summability of the lattice weights -/

/-- A Schwartz factor times a bounded family of coefficients is summable on the lattice. -/
lemma summable_int_schwartz_mul_bounded (ψ : SchwartzMap ℝ ℂ) (b : ℤ → ℂ) {B : ℝ}
    (hb : ∀ m : ℤ, ‖b m‖ ≤ B) (x : ℝ) :
    Summable (fun m : ℤ => ψ (x - (m : ℝ)) * b m) := by
  refine Summable.of_norm_bounded ((summable_int_norm_schwartz_sub ψ x).mul_right B) (fun m => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb m) (norm_nonneg _)

/-! ## The "integral ≤ samples" comparison for amplitudes -/

theorem vrsdIntegralLeSamples (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ → ℝ → ℂ),
      (∀ n : ℕ, MeasureTheory.Integrable (W n)) →
      (∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → W n ξ = 0) →
      (∫⁻ x : ℝ, (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)) ^ p)
        ≤ ENNReal.ofReal C * ∑' m : ℤ,
            (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => FourierTransformInv.fourierInv (W n) ((m : ℤ) : ℝ))) ^ p := by
  obtain ⟨A, hApos, hAbound⟩ := Commons.Analysis.Fourier.schwartz_lattice_sum_bound
    Work.KMTAreas.A7Rep.samplingKernel
  refine ⟨A ^ (p - 1) * (∫ x : ℝ, ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) x‖) + 1,
    ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ A ^ (p - 1) := Real.rpow_nonneg hApos.le _
    have h2 : (0 : ℝ) ≤ ∫ x : ℝ, ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) x‖ :=
      integral_nonneg (fun x => norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]
  intro W hWint hWband
  set ψ : SchwartzMap ℝ ℂ := Work.KMTAreas.A7Rep.samplingKernel with hψdef
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hr0 : (0 : NNReal) < r := lt_of_lt_of_le zero_lt_one hr
  have hψ1 : ∀ ξ ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4),
      FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 1 := by
    intro ξ hξ
    rw [hψdef, fourier_samplingKernel]
    exact Work.KMTAreas.A7Rep.samplingChi_one ξ hξ
  have hψs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) →
      FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 0 := by
    intro ξ hξ
    rw [hψdef, fourier_samplingKernel]
    exact Work.KMTAreas.A7Rep.samplingChi_zero ξ hξ
  have hcontW : ∀ n : ℕ, Continuous (fun x : ℝ => FourierTransformInv.fourierInv (W n) x) := by
    intro n
    have h1 : (⇑(Real.Lp.fourierTransformInv
        (MemLp.toLp (W n) (memLp_one_iff_integrable.mpr (hWint n)))) : ℝ → ℂ)
        = FourierTransformInv.fourierInv (W n) := Real.Lp.fourierTransformInv_toLp _
    rw [← h1]
    exact (Real.Lp.fourierTransformInv _).continuous
  have hbdd : ∀ (n : ℕ) (x : ℝ),
      ‖FourierTransformInv.fourierInv (W n) x‖ ≤ ∫ η : ℝ, ‖W n η‖ := by
    intro n x
    rw [Real.fourierInv_eq']
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.inner_apply, smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set G : ℝ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => FourierTransformInv.fourierInv (W n) x) with hG
  have hGmeas : AEMeasurable G volume := by
    rw [hG]
    exact Submission.PointwiseErgodicTheorems.aemeasurable_variationalNorm hr0
      (fun n => (hcontW n).aemeasurable)
  -- the pointwise sampling bound
  have hsample : ∀ x : ℝ, G x ≤ ∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ * G ((m : ℤ) : ℝ) := by
    intro x
    have hrep : (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
        = fun n : ℕ => ∑' m : ℤ, (ψ : ℝ → ℂ) (x - ((m : ℤ) : ℝ)) *
            FourierTransformInv.fourierInv (W n) ((m : ℤ) : ℝ) := by
      funext n
      exact fourierInv_lattice_reproduction (W n) (hWint n) (by norm_num) (hWband n) ψ
        hψ1 hψs x
    have hyoung := variationalNorm_tsum_mul_le (r := r) hr
      (k := fun m : ℤ => (ψ : ℝ → ℂ) (x - ((m : ℤ) : ℝ)))
      (w := fun m : ℤ => fun n : ℕ => FourierTransformInv.fourierInv (W n) ((m : ℤ) : ℝ))
      (fun n => summable_int_schwartz_mul_bounded ψ
        (fun m : ℤ => FourierTransformInv.fourierInv (W n) ((m : ℤ) : ℝ))
        (fun m => hbdd n _) x)
    simpa only [hG, hrep] using hyoung
  have hsample' : ∀ x : ℝ, G x
      ≤ ∑' m : ℤ, G ((m : ℤ) : ℝ) * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := fun x =>
    (hsample x).trans (le_of_eq (tsum_congr (fun m => mul_comm _ _)))
  have hsumψ : ∀ y : ℝ, Summable (fun m : ℤ => ‖ψ (y - (m : ℝ))‖) :=
    fun y => summable_int_norm_schwartz_sub ψ y
  have hWt : ∀ y : ℝ, (∑' m : ℤ, ‖ψ (y - (m : ℝ))‖ₑ) ≤ ENNReal.ofReal A := by
    intro y
    rw [show (∑' m : ℤ, ‖ψ (y - (m : ℝ))‖ₑ)
          = ∑' m : ℤ, ENNReal.ofReal ‖ψ (y - (m : ℝ))‖ from
        tsum_congr (fun m => by rw [ofReal_norm]),
      ← ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) (hsumψ y)]
    exact ENNReal.ofReal_le_ofReal (hAbound y)
  set Wt : ENNReal := ∫⁻ x : ℝ, ‖ψ x‖ₑ with hWtdef
  have hW_eq : Wt = ENNReal.ofReal (∫ x : ℝ, ‖ψ x‖) := by
    rw [hWtdef, show (fun x : ℝ => ‖ψ x‖ₑ) = fun x => ENNReal.ofReal ‖ψ x‖ from
        funext (fun x => by rw [ofReal_norm]),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ψ.integrable.norm
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))]
  have hWx : ∀ m : ℤ, (∫⁻ x : ℝ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) = Wt := by
    intro m
    rw [hWtdef]
    exact lintegral_sub_right_eq_self (fun y : ℝ => ‖ψ y‖ₑ) ((m : ℤ) : ℝ)
  have hmain : ∀ x : ℝ, G x ^ p
      ≤ (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
    intro x
    have hf : AEMeasurable (fun m : ℤ => G ((m : ℤ) : ℝ)) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have hw : AEMeasurable (fun m : ℤ => ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have h1 := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral_measure
      (Measure.count : Measure ℤ) hp hf hw
    rw [lintegral_count, lintegral_count, lintegral_count] at h1
    exact (ENNReal.rpow_le_rpow (hsample' x) (le_of_lt hp0)).trans h1
  have hstep1 : ∫⁻ x : ℝ, G x ^ p
      ≤ ∫⁻ x : ℝ, (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ :=
    lintegral_mono hmain
  have hstep2 : ∫⁻ x : ℝ, (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
        ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
    apply lintegral_mono; intro x
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hWt x) hp1) bot_le
  have hmeasc : ∀ m : ℤ, AEMeasurable
      (fun x : ℝ => G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) volume := by
    intro m
    have h2 : AEMeasurable (fun x : ℝ => ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) volume :=
      (((ψ.continuous.comp (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable
    exact aemeasurable_const.mul h2
  have hfinal : ∫⁻ x : ℝ, G x ^ p
      ≤ ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) + 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
    calc ∫⁻ x : ℝ, G x ^ p
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ :=
          hstep1.trans hstep2
      _ = ENNReal.ofReal A ^ (p - 1) *
            ∫⁻ x : ℝ, ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
          rw [lintegral_const_mul'' _ (AEMeasurable.tsum hmeasc)]
      _ = ENNReal.ofReal A ^ (p - 1) *
            ∑' m : ℤ, ∫⁻ x : ℝ,
              G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
          rw [lintegral_tsum hmeasc]
      _ = ENNReal.ofReal A ^ (p - 1) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ∫⁻ x : ℝ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
          congr 1
          apply tsum_congr; intro m
          exact lintegral_const_mul'' _ (by
            exact (((ψ.continuous.comp
              (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable)
      _ = ENNReal.ofReal A ^ (p - 1) * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * Wt := by
          congr 1
          apply tsum_congr; intro m
          rw [hWx m]
      _ = ENNReal.ofReal A ^ (p - 1) * (Wt * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p) := by
          congr 1
          rw [ENNReal.tsum_mul_right, mul_comm]
      _ = ENNReal.ofReal A ^ (p - 1) * Wt * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
          rw [mul_assoc]
      _ = ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖)) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
          rw [hW_eq, ENNReal.ofReal_rpow_of_nonneg hApos.le hp1,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hApos.le _)]
      _ ≤ ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) + 1) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
          apply mul_le_mul_of_nonneg_right _ bot_le
          exact ENNReal.ofReal_le_ofReal (by linarith)
  simpa only [hG, hψdef] using hfinal

end

end Work.KMTAreas.A7Hi
