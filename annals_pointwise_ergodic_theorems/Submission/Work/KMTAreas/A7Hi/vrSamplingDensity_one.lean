import Mathlib
import Submission.Work.KMTAreas.A7Hi.vrSamplingDensity

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-! ## The `p = 1` endpoint of the amplitude-form sampling comparison

`Work.KMTAreas.A7Hi.vrsdSamplesLeIntegral` proves, for `p > 1`, the comparison
`∑_m (Vʳ(𝓕⁻ W m))^p ≤ C ∫ (Vʳ(𝓕⁻ W x))^p` for a family of *integrable amplitudes* `W`
supported in the sub-Nyquist band `[-1/4,1/4]`.  The proof there goes
through the weighted reproducing bound of `Commons.Analysis.Fourier.norm_fourierInv_le_weighted`
and then a weighted Hölder step, which requires `p > 1`.

At `p = 1` no Hölder step is needed: the *exact* reproducing identity with the fixed sampling
kernel `K = 𝓕⁻ samplingChi` of `Work.KMTAreas.A7Rep` together with Minkowski's inequality for the
variational norm gives the pointwise bound
`Vʳ(𝓕⁻ W · x) ≤ ∫⁻ y, Vʳ(𝓕⁻ W · y) · ‖K (x - y)‖ₑ`,
and *then* one sums over the lattice and uses Tonelli with the uniform lattice bound
`∑_m ‖K (u - m)‖ₑ ≤ ofReal A` of `Work.KMTAreas.A7Rep.samplingKernel_latticeBoundENN`. -/

/-- **Reproducing identity against a band-limited integrable amplitude.**  If `W` is integrable
and vanishes outside the band `[-1/4,1/4]`, and the integrable kernel `w` has `𝓕w ≡ 1` on the
support of `W`, then `𝓕⁻W x = ∫ y, 𝓕⁻W y · w (x - y)` (a Fubini computation on the amplitude
side). -/
private lemma fourierInv_reproducing_kernel {W w : ℝ → ℂ} (hW : MeasureTheory.Integrable W)
    (hw : MeasureTheory.Integrable w)
    (hprod : ∀ β : ℝ, W β ≠ 0 → FourierTransform.fourier w β = 1) (x : ℝ) :
    ∫ y : ℝ, FourierTransformInv.fourierInv W y * w (x - y)
      = FourierTransformInv.fourierInv W x := by
  have hinner : ∀ β : ℝ,
      (∫ y : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) * w (x - y))
        = Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I)
            * FourierTransform.fourier w β := by
    intro β
    set K : ℝ → ℂ := fun z => Complex.exp (↑(-2 * Real.pi * inner ℝ z β) * Complex.I) * w z
      with hKdef
    have hK : ∫ z : ℝ, K z = FourierTransform.fourier w β := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with z
      rw [hKdef]
      simp only [smul_eq_mul]
    have hstep : (∫ y : ℝ,
          Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) * w (x - y))
        = Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I) * ∫ y : ℝ, K (x - y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [hKdef]
      have hexp : Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I)
          = Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I)
            * Complex.exp (↑(-2 * Real.pi * inner ℝ (x - y) β) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        rw [Real.inner_apply, Real.inner_apply, Real.inner_apply]
        push_cast
        ring
      rw [hexp]; ring
    calc (∫ y : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) * w (x - y))
        = Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I) * ∫ y : ℝ, K (x - y) := hstep
      _ = Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I) * ∫ z : ℝ, K z := by
          rw [integral_sub_left_eq_self K volume x]
      _ = Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I)
            * FourierTransform.fourier w β := by rw [hK]
  have hprodint : MeasureTheory.Integrable (Function.uncurry
      (fun y β : ℝ =>
        (Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β) * w (x - y)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.Integrable.mul_prod
        (hw.norm.comp_sub_left x) hW.norm) ?_ ?_
    · have h1 : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        (by fun_prop : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I))).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2)
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        hW.aestronglyMeasurable.comp_snd
      have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => w (x - p.1))
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        (hw.comp_sub_left x).aestronglyMeasurable.comp_fst
      have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I) * W p.2
            * w (x - p.1)) (MeasureTheory.volume.prod MeasureTheory.volume) := by
        have hfun : (((fun p : ℝ × ℝ =>
              Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I))
            * (fun p : ℝ × ℝ => W p.2))
            * (fun p : ℝ × ℝ => w (x - p.1)))
            = (fun p : ℝ × ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I)
                * W p.2 * w (x - p.1)) := by
          funext p; rfl
        rw [← hfun]
        exact (h1.mul h2).mul h3
      exact hm
    · filter_upwards with p
      simp only [Function.uncurry, smul_eq_mul, norm_mul,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_of_eq (mul_comm _ _)
  have hswap := MeasureTheory.integral_integral_swap hprodint
  have hrep : ∫ y : ℝ, FourierTransformInv.fourierInv W y * w (x - y)
      = FourierTransformInv.fourierInv W x := by
    calc ∫ y : ℝ, FourierTransformInv.fourierInv W y * w (x - y)
        = ∫ y : ℝ, (∫ β : ℝ,
              Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β)
              * w (x - y) := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Real.fourierInv_eq']
      _ = ∫ y : ℝ, ∫ β : ℝ,
              (Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β)
                * w (x - y) := by
          apply integral_congr_ae
          filter_upwards with y
          rw [MeasureTheory.integral_mul_const (w (x - y)) (fun β : ℝ =>
            Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β)]
      _ = ∫ β : ℝ, ∫ y : ℝ,
              (Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β)
                * w (x - y) := hswap
      _ = ∫ β : ℝ, W β *
              (∫ y : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I)
                * w (x - y)) := by
          apply integral_congr_ae
          filter_upwards with β
          rw [show (fun y : ℝ =>
                (Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β) * w (x - y))
              = fun y => W β * (Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I)
                * w (x - y)) by
            funext y; rw [smul_eq_mul]; ring]
          rw [MeasureTheory.integral_const_mul (W β) (fun y : ℝ =>
            Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) * w (x - y))]
      _ = ∫ β : ℝ, W β * Complex.exp (↑(2 * Real.pi * inner ℝ β x) * Complex.I) := by
          apply integral_congr_ae
          filter_upwards with β
          rw [hinner β]
          by_cases hβ : W β = 0
          · rw [hβ, zero_mul, zero_mul]
          · rw [hprod β hβ, mul_one]
      _ = FourierTransformInv.fourierInv W x := by
          rw [Real.fourierInv_eq']
          apply integral_congr_ae
          filter_upwards with β
          rw [smul_eq_mul, mul_comm]
  exact hrep

/-- The inverse Fourier transform of an integrable amplitude is continuous. -/
private lemma continuous_fourierInv_of_integrable' {W : ℝ → ℂ} (hW : MeasureTheory.Integrable W) :
    Continuous (fun x : ℝ => FourierTransformInv.fourierInv W x) := by
  have h1 : (⇑(Real.Lp.fourierTransformInv
      (MemLp.toLp W (memLp_one_iff_integrable.mpr hW))) : ℝ → ℂ)
      = FourierTransformInv.fourierInv W := Real.Lp.fourierTransformInv_toLp _
  rw [← h1]
  exact (Real.Lp.fourierTransformInv _).continuous

/-- **The pointwise reproducing bound for the variational norm, amplitude form.**  For `1 ≤ r`,
every family `W : ℕ → ℝ → ℂ` of integrable amplitudes supported in `[-1/4,1/4]` satisfies

  `Vʳ_n (𝓕⁻(W n) x) ≤ ∫⁻ y, Vʳ_n (𝓕⁻(W n) y) · ‖K (x - y)‖ₑ`,

where `K = 𝓕⁻ samplingChi` is the fixed sampling kernel of `Work.KMTAreas.A7Rep` (`𝓕 K ≡ 1` on
`[-1/4,1/4]`).  This is Minkowski's inequality (`variationalNorm_integral_le`) applied to the
reproducing identity `fourierInv_reproducing_kernel`; no constant appears because the *exact*
kernel weight `‖K (x - y)‖ₑ` is used. -/
private theorem vrPointwiseWeighted_aux (r : NNReal) (hr : 1 ≤ r) :
    ∀ (W : ℕ → ℝ → ℂ), (∀ n : ℕ, MeasureTheory.Integrable (W n)) →
      (∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → W n ξ = 0) →
      ∀ x : ℝ,
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
          ≤ ∫⁻ y : ℝ, PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => FourierTransformInv.fourierInv (W n) y)
              * ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (x - y)‖ₑ := by
  intro W hW hsupp x
  set ker : ℝ → ℂ := (Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) with hker
  have hkerint : MeasureTheory.Integrable ker := by
    rw [hker]; exact Work.KMTAreas.A7Rep.samplingKernel.integrable
  have hkerfour : ∀ β : ℝ, β ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) →
      FourierTransform.fourier ker β = 1 := by
    have hfourier : FourierTransform.fourier
          (⇑(FourierTransformInv.fourierInv Work.KMTAreas.A7Rep.samplingChi))
        = ⇑Work.KMTAreas.A7Rep.samplingChi := by
      rw [← SchwartzMap.fourier_coe
        (FourierTransformInv.fourierInv Work.KMTAreas.A7Rep.samplingChi)]
      exact congrArg DFunLike.coe
        (FourierTransform.fourier_fourierInv_eq Work.KMTAreas.A7Rep.samplingChi)
    intro β hβ
    change FourierTransform.fourier
      (⇑(FourierTransformInv.fourierInv Work.KMTAreas.A7Rep.samplingChi)) β = 1
    rw [congrFun hfourier β]
    exact Work.KMTAreas.A7Rep.samplingChi_one β hβ
  have hprod : ∀ (n : ℕ) (β : ℝ), W n β ≠ 0 → FourierTransform.fourier ker β = 1 := by
    intro n β hβ
    apply hkerfour β
    by_contra hcon
    exact hβ (hsupp n β hcon)
  have hcont : ∀ n : ℕ, Continuous (fun y : ℝ => FourierTransformInv.fourierInv (W n) y) :=
    fun n => continuous_fourierInv_of_integrable' (hW n)
  set C₀ : ℕ → ℝ := fun n => ∫ β : ℝ, ‖W n β‖ with hC₀
  have hbddW : ∀ (n : ℕ) (y : ℝ), ‖FourierTransformInv.fourierInv (W n) y‖ ≤ C₀ n := by
    intro n y
    rw [hC₀]
    rw [Real.fourierInv_eq']
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with β
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hintg : ∀ n : ℕ, MeasureTheory.Integrable
      (fun y : ℝ => FourierTransformInv.fourierInv (W n) y * ker (x - y)) := by
    intro n
    exact (hkerint.comp_sub_left x).bdd_mul (hcont n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbddW n))
  have hMink : PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ y : ℝ, FourierTransformInv.fourierInv (W n) y * ker (x - y))
      ≤ ∫⁻ y : ℝ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) y * ker (x - y)) :=
    Work.KMTAreas.A7.variationalNorm_integral_le (r := r) hr (ν := volume) hintg
  have hrewrite : (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
      = fun n : ℕ => ∫ y : ℝ, FourierTransformInv.fourierInv (W n) y * ker (x - y) :=
    funext (fun n => (fourierInv_reproducing_kernel (hW n) hkerint (hprod n) x).symm)
  have hintegrand : ∀ y : ℝ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => FourierTransformInv.fourierInv (W n) y * ker (x - y))
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) y) * ‖ker (x - y)‖ₑ := by
    intro y
    have hfun : (fun n : ℕ => FourierTransformInv.fourierInv (W n) y * ker (x - y))
        = ker (x - y) • (fun n : ℕ => FourierTransformInv.fourierInv (W n) y) := by
      funext n; rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hfun, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr]
    exact mul_comm _ _
  calc PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∫ y : ℝ, FourierTransformInv.fourierInv (W n) y * ker (x - y)) := by
        rw [hrewrite]
    _ ≤ ∫⁻ y : ℝ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) y * ker (x - y)) := hMink
    _ = ∫⁻ y : ℝ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) y) * ‖ker (x - y)‖ₑ :=
        lintegral_congr hintegrand
    _ = ∫⁻ y : ℝ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) y)
            * ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (x - y)‖ₑ := by
        rw [hker]

/-- **The `Vʳ`-lattice sampling comparison at the endpoint exponent `p = 1`, in amplitude form.**
For `1 ≤ r` there is `C > 0` such that for every family `W : ℕ → ℝ → ℂ` of *integrable* amplitudes
supported in the band `[-1/4,1/4]`, writing `f n := 𝓕⁻(W n)`,

  `∑'_m Vʳ_n (f n m) ≤ C · ∫⁻_ℝ Vʳ_n (f n x)`.

This is the `p = 1` companion of `Work.KMTAreas.A7Hi.vrsdSamplesLeIntegral`. -/
theorem vrsdSamplesLeIntegral_one (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ → ℝ → ℂ),
      (∀ n : ℕ, MeasureTheory.Integrable (W n)) →
      (∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → W n ξ = 0) →
      (∑' m : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) ((m : ℤ) : ℝ)))
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ,
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => FourierTransformInv.fourierInv (W n) x) := by
  obtain ⟨Ck, hCkpos, hCkdec⟩ := Work.KMTAreas.A7Rep.samplingKernel_decay
  obtain ⟨A, hApos, _hAmass, hAlat⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_kernel_lattice_weight_le
      (Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) Ck hCkpos hCkdec
  refine ⟨A, hApos, ?_⟩
  intro W hW hsupp
  have hr0 : (0 : NNReal) < r := lt_of_lt_of_le zero_lt_one hr
  set G : ℝ → ℝ≥0∞ := fun x =>
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
    with hG
  have hGmeas : AEMeasurable G volume := by
    rw [hG]
    exact Submission.PointwiseErgodicTheorems.aemeasurable_variationalNorm hr0
      (fun n => (continuous_fourierInv_of_integrable' (hW n)).aemeasurable)
  have hKint : MeasureTheory.Integrable (Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) :=
    Work.KMTAreas.A7Rep.samplingKernel.integrable
  have hwmeas : ∀ c : ℝ,
      AEMeasurable (fun t : ℝ => ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (c - t)‖ₑ)
        volume := by
    intro c
    have h1 : AEMeasurable (Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ)
        (Measure.map (fun t : ℝ => c - t) volume) := by
      rw [Measure.map_sub_left_eq_self]
      exact hKint.aemeasurable
    exact (h1.comp_measurable (measurable_const.sub measurable_id)).enorm
  have hpoint : ∀ x : ℝ, G x ≤ ∫⁻ y : ℝ, G y *
      ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (x - y)‖ₑ := by
    intro x
    rw [hG]
    exact vrPointwiseWeighted_aux r hr W hW hsupp x
  have hlatt : ∀ y : ℝ,
      (∑' m : ℤ, ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) ((m : ℝ) - y)‖ₑ)
        ≤ ENNReal.ofReal A := fun y => hAlat y
  have hmeas_summand : ∀ m : ℤ, AEMeasurable
      (fun y : ℝ => G y * ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) ((m : ℝ) - y)‖ₑ)
      volume := fun m => hGmeas.mul (hwmeas ((m : ℝ)))
  calc (∑' m : ℤ, G ((m : ℤ) : ℝ))
      ≤ ∑' m : ℤ, ∫⁻ y : ℝ, G y *
          ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (((m : ℤ) : ℝ) - y)‖ₑ :=
        ENNReal.tsum_le_tsum (fun m => hpoint _)
    _ = ∫⁻ y : ℝ, ∑' m : ℤ, G y *
          ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (((m : ℤ) : ℝ) - y)‖ₑ :=
        (MeasureTheory.lintegral_tsum hmeas_summand).symm
    _ = ∫⁻ y : ℝ, G y * (∑' m : ℤ,
          ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) (((m : ℤ) : ℝ) - y)‖ₑ) := by
        apply lintegral_congr; intro y
        rw [ENNReal.tsum_mul_left]
    _ ≤ ∫⁻ y : ℝ, G y * ENNReal.ofReal A := by
        apply lintegral_mono; intro y
        exact mul_le_mul_of_nonneg_left (hlatt y) bot_le
    _ = ENNReal.ofReal A * ∫⁻ y : ℝ, G y := by
        rw [MeasureTheory.lintegral_mul_const'' _ hGmeas, mul_comm]

/-! ## The `p = 1` decimated sampling density comparison -/

/-- **The decimated sampling density comparison at the endpoint exponent `p = 1`.**

For `1 ≤ r` there is `C > 0` such that for every family `F : ℕ → ℝ → ℂ` of functions whose
inverse Fourier transforms are supported in `[-β,β]` (with `β < 1/2`), every `q ≥ 1` with
`β q ≤ 1/4`, and every residue `a : ℤ`,

  `∑'_t Vʳ_n (F n (a + q t)) ≤ C · q⁻¹ · ∫⁻_ℝ Vʳ_n (F n x) dx`.

The proof rescales the family, `W n := rescAmp q a (g n)` (whose amplitude is supported in
`[-1/4,1/4]`), applies the endpoint amplitude-form sampling comparison
`Work.KMTAreas.A7Hi.vrsdSamplesLeIntegral_one`, and converts the lattice sum over the progression
`a + qℤ` into the sum over `ℤ` with the affine substitution `∫⁻ u, A (a + q u) = q⁻¹ ∫⁻ x, A x`
of the Lebesgue integral. -/
theorem vrSamplingDensity_one (r : NNReal) (hr : 1 ≤ r) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ → ℂ)
      (hF : ∀ n : ℕ, Work.KMTAreas.A7Rep.HasRealFreqSupport (F n) (Set.Icc (-β) β))
      (q : ℕ) (hq : 0 < q) (hβq : β * (q : ℝ) ≤ 1 / 4) (a : ℤ),
      (∑' t : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * (t : ℝ))))
        ≤ ENNReal.ofReal C * (q : ENNReal)⁻¹ * ∫⁻ x : ℝ,
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := vrsdSamplesLeIntegral_one r hr
  refine ⟨C₁, hC₁pos, ?_⟩
  intro F hF q hq hβq a
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [Work.KMTAreas.A7Rep.HasRealFreqSupport] at hF
  choose g hgint hgsupp hgF using hF
  set W : ℕ → ℝ → ℂ := fun n => rescAmp (q : ℝ) (a : ℝ) (g n) with hW
  have hWint : ∀ n : ℕ, MeasureTheory.Integrable (W n) := by
    intro n
    simp only [hW]
    exact integrable_rescAmp (hgint n) hqR
  have hWsupp : ∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → W n ξ = 0 := by
    intro n ξ hξ
    simp only [hW]
    exact rescAmp_eq_zero (hgsupp n) hqR hβq hξ
  have hWfourier : ∀ (n : ℕ) (u : ℝ),
      FourierTransformInv.fourierInv (W n) u = F n ((a : ℝ) + (q : ℝ) * u) := by
    intro n u
    simp only [hW]
    rw [fourierInv_rescAmp (g n) hqR u]
    exact (hgF n ((a : ℝ) + (q : ℝ) * u)).symm
  have hA : ∀ x : ℝ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => FourierTransformInv.fourierInv (W n) x)
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * x)) := by
    intro x
    congr 1
    funext n
    exact hWfourier n x
  have hsample : ∀ t : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * (t : ℝ)))
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) ((t : ℤ) : ℝ)) :=
    fun t => (hA ((t : ℤ) : ℝ)).symm
  have hsub := lintegral_comp_add_mul
    (fun x : ℝ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x))
    ((a : ℤ) : ℝ) hqR
  calc (∑' t : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => F n ((a : ℝ) + (q : ℝ) * (t : ℝ))))
      = ∑' t : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) ((t : ℤ) : ℝ)) :=
        tsum_congr hsample
    _ ≤ ENNReal.ofReal C₁ * ∫⁻ x : ℝ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => FourierTransformInv.fourierInv (W n) x) := hC₁ W hWint hWsupp
    _ = ENNReal.ofReal C₁ * ((ENNReal.ofReal ((q : ℕ) : ℝ))⁻¹ * ∫⁻ x : ℝ,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x)) := by
        congr 1
        rw [← hsub]
        apply lintegral_congr
        intro x
        rw [hA x]
    _ = ENNReal.ofReal C₁ * (q : ENNReal)⁻¹ * ∫⁻ x : ℝ,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => F n x) := by
        rw [ENNReal.ofReal_natCast, mul_assoc]

end

end Work.KMTAreas.A7Hi
