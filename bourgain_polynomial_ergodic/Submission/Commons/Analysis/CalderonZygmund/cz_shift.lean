import Mathlib
import Submission.Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d_banach
import Submission.Commons.Analysis.CalderonZygmund.lacunary_shifted_kernel_sum_le
import Submission.Commons.Analysis.CalderonZygmund.czSymb_bound_uniform
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
import Submission.Commons.Analysis.Fourier.plancherel_integrable_memLp_two
import Submission.Commons.Analysis.Schwartz.fourierInv_schwartz_decay
import Submission.Commons.Analysis.Schwartz.fourierInv_schwartz_decay_controlled
import Submission.Commons.MeasureTheory.Function.eLpNorm_integral_le_lintegral_eLpNorm
import Submission.Commons.Analysis.Measure.finset_lintegral_enorm_le_ofReal_sum
import Submission.Commons.Analysis.Lp.rpow_marcinkiewicz_const_le
import Submission.Commons.Analysis.Lp.eLpNorm_pairing_le
import Submission.Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
import Submission.Commons.Analysis.Convolution.integral_inner_convolution_eq_adjoint_meas
import Submission.Commons.Analysis.CalderonZygmund.cz_weak_type_one_lintegral

namespace Commons.Analysis.CalderonZygmund

open _root_.MeasureTheory Filter
open scoped ENNReal FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section


def czE (x ξ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x * ξ))

lemma norm_czE (a ξ : ℝ) : ‖czE a ξ‖ = 1 := by
  rw [czE]
  rw [show (2 * Real.pi * Complex.I * (a * ξ)) = ((2 * Real.pi * a * ξ : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_czE (a : ℝ) : Continuous fun ξ : ℝ => czE a ξ := by
  unfold czE
  fun_prop

lemma czE_add (a b ξ : ℝ) : czE (a + b) ξ = czE a ξ * czE b ξ := by
  rw [czE, czE, czE, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma czE_eq_exp_neg (x ξ : ℝ) : czE x ξ = Complex.exp ((↑(-2 * Real.pi * ξ * (-x))) * Complex.I) := by
  rw [czE]
  congr 1
  push_cast
  ring

lemma eLpNorm_comp_neg_two {H : Type*} [NormedAddCommGroup H] (f : ℝ → H) :
    eLpNorm (fun x => f (-x)) (2 : ℝ≥0∞) (volume : Measure ℝ)
      = eLpNorm f (2 : ℝ≥0∞) (volume : Measure ℝ) := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  by_cases hf : AEStronglyMeasurable f (volume : Measure ℝ)
  swap
  · have hf' : ¬ AEStronglyMeasurable (fun x => f (-x)) (volume : Measure ℝ) := by
      intro h
      apply hf
      have h2 := h.comp_measurePreserving hmp
      simpa [Function.comp_def] using h2
    rw [eLpNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable hf']
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
        (f := fun x => f (-x)) (hf.comp_measurePreserving hmp),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hf]
  congr 1
  rw [show ((2:ℝ≥0∞).toReal) = (2:ℝ) by norm_num]
  have hmap : Measure.map (⇑(MeasurableEquiv.neg ℝ)) (volume : Measure ℝ) = volume := by
    rw [show (⇑(MeasurableEquiv.neg ℝ)) = (fun x : ℝ => -x) from rfl, Measure.map_neg_eq_self]
  have h := MeasureTheory.lintegral_map_equiv (μ := (volume : Measure ℝ))
      (f := fun y : ℝ => ‖f y‖ₑ ^ (2:ℝ)) (MeasurableEquiv.neg ℝ)
  rw [hmap] at h
  exact h.symm

lemma norm_fourier_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (f : ℝ → H) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with x
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma eLpNorm_fourier_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (h : ℝ → H) (h1 : Integrable h) (h2 : MemLp h 2 (volume : Measure ℝ)) :
    eLpNorm (𝓕 h) (ENNReal.ofReal 2) (volume : Measure ℝ)
      = eLpNorm h (ENNReal.ofReal 2) (volume : Measure ℝ) := by
  have hrefl : eLpNorm (fun x : ℝ => (𝓕⁻ h) (-x)) (ENNReal.ofReal 2) volume
      = eLpNorm (𝓕⁻ h) (ENNReal.ofReal 2) volume := by
    rw [show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) by norm_num]
    exact eLpNorm_comp_neg_two _
  have hid : 𝓕 h = fun x : ℝ => (𝓕⁻ h) (-x) := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [eLpNorm_congr_ae (Filter.EventuallyEq.of_eq hid), hrefl,
    Commons.Analysis.Fourier.plancherel_integrable_memLp_two h h1 h2]

lemma continuous_fourier_of_integrable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {f : ℝ → H} (hf : Integrable f) : Continuous (𝓕 f) := by
  have hinv : Continuous (𝓕⁻ f) := by
    rw [show 𝓕⁻ f = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ) f from rfl]
    refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_ hf
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  have hid : 𝓕 f = fun x : ℝ => (𝓕⁻ f) (-x) := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [hid]
  exact hinv.comp continuous_neg

def czKern (m : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ ξ, m ξ * czE x ξ

def czOp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (K : ℝ → ℂ) (f : ℝ → H) : ℝ → H :=
  fun x => ∫ y, K (x - y) • f y

theorem czOp_czKern_eq_mult {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (m : ℝ → ℂ) (hm : Integrable m) (b : ℝ → H) (hb : Integrable b) :
    czOp (czKern m) b = fun x => ∫ ξ, (m ξ * czE x ξ) • 𝓕 b ξ := by
  funext x
  have hR : (∫ ξ, (m ξ * czE x ξ) • 𝓕 b ξ)
      = ∫ ξ, ∫ v, (m ξ * czE (x - v) ξ) • b v := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with v
    rw [smul_smul]
    congr 1
    rw [mul_assoc]
    rw [show Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) = czE (-v) ξ from by
      rw [czE_eq_exp_neg]; congr 1; push_cast; ring]
    rw [← czE_add]
    rw [sub_eq_add_neg]
  rw [hR]
  rw [show czOp (czKern m) b x = ∫ v, (∫ ξ, m ξ * czE (x - v) ξ) • b v from rfl]
  have hint : Integrable (Function.uncurry fun (ξ v : ℝ) => (m ξ * czE (x - v) ξ) • b v)
      (volume.prod volume) := by
    refine Integrable.mono' ((hm.norm).mul_prod hb.norm) ?_ ?_
    · have h1 : Continuous fun p : ℝ × ℝ => czE (x - p.2) p.1 := by unfold czE; fun_prop
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => m p.1) (volume.prod volume) :=
        hm.aestronglyMeasurable.comp_fst
      exact (h2.mul h1.measurable.aestronglyMeasurable).smul hb.aestronglyMeasurable.comp_snd
    · filter_upwards with p
      rcases p with ⟨ξ, v⟩
      rw [Function.uncurry_apply_pair, norm_smul, norm_mul, norm_czE, mul_one]
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards with v
  rw [integral_smul_const]

theorem czOp_czKern_eq_fourierInv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (m : ℝ → ℂ) (hm : Integrable m) (f : ℝ → H) (hf : Integrable f) :
    czOp (czKern m) f = 𝓕⁻ (fun ξ => m ξ • 𝓕 f ξ) := by
  rw [czOp_czKern_eq_mult m hm f hf]
  funext x
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [smul_smul, czE_eq_exp_neg, mul_comm]

/-- If `f` is in `L¹` and bounded by `C`, then it is in `L²`. -/
lemma memLp_two_of_memLp_one_of_ae_bound {H : Type*} [NormedAddCommGroup H] {f : ℝ → H} {C : ℝ}
    (hC : 0 ≤ C) (h1 : MemLp f 1 (volume : Measure ℝ))
    (hb : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖f ξ‖ ≤ C) : MemLp f 2 (volume : Measure ℝ) := by
  rw [memLp_iff]
  rw [lt_top_iff_ne_top]
  have hfin : ∫⁻ ξ : ℝ, ‖f ξ‖ₑ < ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm h1.aestronglyMeasurable]
    exact h1.eLpNorm_lt_top
  have hmono : ∫⁻ ξ : ℝ, ‖f ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal C * ∫⁻ ξ : ℝ, ‖f ξ‖ₑ := by
    rw [← lintegral_const_mul'' _ h1.aestronglyMeasurable.enorm]
    apply lintegral_mono_ae
    filter_upwards [hb] with ξ hξ
    have h1 : ‖f ξ‖ₑ ≤ ENNReal.ofReal C := by
      rw [← ofReal_norm (f ξ)]
      exact ENNReal.ofReal_le_ofReal hξ
    calc ‖f ξ‖ₑ ^ (2:ℝ) ≤ ‖f ξ‖ₑ * ENNReal.ofReal C := by
          rw [ENNReal.rpow_two, pow_two]
          exact mul_le_mul_of_nonneg_left h1 bot_le
      _ = ENNReal.ofReal C * ‖f ξ‖ₑ := mul_comm _ _
  have hlt : ∫⁻ ξ : ℝ, ‖f ξ‖ₑ ^ (2:ℝ) < ⊤ :=
    lt_of_le_of_lt hmono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) h1.aestronglyMeasurable,
    show ((2:ℝ≥0∞).toReal) = (2:ℝ) by norm_num]
  exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hlt))

theorem czOp_czKern_L2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (m : ℝ → ℂ) (B : ℝ) (hB : 0 < B) (hmb : ∀ ξ, ‖m ξ‖ ≤ B) (hm : Integrable m)
    (f : ℝ → H) (hf : Integrable f) :
    eLpNorm (czOp (czKern m) f) (ENNReal.ofReal 2) (volume : Measure ℝ)
      ≤ ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal 2) (volume : Measure ℝ) := by
  by_cases hf2 : eLpNorm f (ENNReal.ofReal 2) (volume : Measure ℝ) = ⊤
  · rw [hf2, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hB)]
    exact le_top
  have hmemf : MemLp f (ENNReal.ofReal 2) (volume : Measure ℝ) := by
    rw [memLp_iff, lt_top_iff_ne_top]
    exact hf2
  have hmemf2 : MemLp f 2 (volume : Measure ℝ) := by
    rwa [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  have hplf : eLpNorm (𝓕 f) (ENNReal.ofReal 2) (volume : Measure ℝ)
      = eLpNorm f (ENNReal.ofReal 2) (volume : Measure ℝ) := eLpNorm_fourier_eq f hf hmemf2
  have hFcont : Continuous (𝓕 f) := continuous_fourier_of_integrable hf
  have hmemF : MemLp (𝓕 f) (ENNReal.ofReal 2) (volume : Measure ℝ) := by
    rw [memLp_iff, lt_top_iff_ne_top, hplf]
    exact hf2
  have hm1 : MemLp m 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hm
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    memLp_two_of_memLp_one_of_ae_bound hB.le hm1
      (Filter.Eventually.of_forall hmb)
  have hGae : AEStronglyMeasurable (fun ξ => m ξ • 𝓕 f ξ) (volume : Measure ℝ) :=
    hm.aestronglyMeasurable.smul hFcont.stronglyMeasurable.aestronglyMeasurable
  have hbound : ∀ ξ, ‖m ξ • 𝓕 f ξ‖ ≤ (∫ x, ‖f x‖) * ‖m ξ‖ := by
    intro ξ
    rw [norm_smul]
    calc ‖m ξ‖ * ‖𝓕 f ξ‖ ≤ ‖m ξ‖ * ∫ x, ‖f x‖ :=
          mul_le_mul_of_nonneg_left (norm_fourier_le f ξ) (norm_nonneg _)
      _ = (∫ x, ‖f x‖) * ‖m ξ‖ := mul_comm _ _
  have hGi1 : MemLp (fun ξ => m ξ • 𝓕 f ξ) 1 (volume : Measure ℝ) :=
    MemLp.of_le_mul (g := m) (c := ∫ x, ‖f x‖) hm1 hGae
      (Filter.Eventually.of_forall hbound)
  have hGi2 : MemLp (fun ξ => m ξ • 𝓕 f ξ) 2 (volume : Measure ℝ) :=
    MemLp.of_le_mul (g := m) (c := ∫ x, ‖f x‖) hm2 hGae
      (Filter.Eventually.of_forall hbound)
  have hGi : Integrable (fun ξ => m ξ • 𝓕 f ξ) := memLp_one_iff_integrable.mp hGi1
  have hplg := Commons.Analysis.Fourier.plancherel_integrable_memLp_two
      (fun ξ => m ξ • 𝓕 f ξ) hGi hGi2
  have hid : czOp (czKern m) f = 𝓕⁻ (fun ξ => m ξ • 𝓕 f ξ) :=
    czOp_czKern_eq_fourierInv m hm f hf
  have hstep : eLpNorm (fun ξ => m ξ • 𝓕 f ξ) (ENNReal.ofReal 2) (volume : Measure ℝ)
      ≤ ENNReal.ofReal B * eLpNorm (𝓕 f) (ENNReal.ofReal 2) (volume : Measure ℝ) := by
    have h1 : eLpNorm (fun ξ => m ξ • 𝓕 f ξ) (ENNReal.ofReal 2) volume
        ≤ eLpNorm (fun ξ => B • 𝓕 f ξ) (ENNReal.ofReal 2) volume := by
      apply eLpNorm_mono_enorm hGae
      intro ξ
      rw [enorm_smul, enorm_smul]
      gcongr
      rw [← ofReal_norm (m ξ), Real.enorm_eq_ofReal hB.le]
      exact ENNReal.ofReal_le_ofReal (hmb ξ)
    have h2 : eLpNorm (fun ξ => B • 𝓕 f ξ) (ENNReal.ofReal 2) volume
        ≤ ENNReal.ofReal B * eLpNorm (𝓕 f) (ENNReal.ofReal 2) volume := by
      refine (eLpNorm_const_smul_le (p := ENNReal.ofReal 2) (μ := volume) (f := 𝓕 f) (c := B)).trans ?_
      rw [Real.enorm_eq_ofReal hB.le]
    exact h1.trans h2
  calc eLpNorm (czOp (czKern m) f) (ENNReal.ofReal 2) volume
      = eLpNorm (𝓕⁻ (fun ξ => m ξ • 𝓕 f ξ)) (ENNReal.ofReal 2) volume := by rw [hid]
    _ = eLpNorm (fun ξ => m ξ • 𝓕 f ξ) (ENNReal.ofReal 2) volume := hplg
    _ ≤ ENNReal.ofReal B * eLpNorm (𝓕 f) (ENNReal.ofReal 2) volume := hstep
    _ = ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal 2) volume := by rw [hplf]


def czPhi (ψ : ℝ → ℂ) : ℝ → ℂ := fun t => ∫ η, ψ η * czE t η

def czSymb (A : ℝ) (d : ℕ) (D : Finset ℝ) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun ξ => ∑ N ∈ D,
    eps N * (ψ (A * N ^ d * ξ) * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))

lemma cz_int_term (ψ : ℝ → ℂ) (u c : ℝ) (hu : 0 < u) :
    (∫ ξ : ℝ, ψ (u * ξ) * czE c ξ) = u⁻¹ * czPhi ψ (c / u) := by
  have hfun : (fun ξ : ℝ => ψ (u * ξ) * czE c ξ)
      = fun ξ => (fun η : ℝ => ψ η * czE (c / u) η) (u * ξ) := by
    funext ξ
    simp only [czE]
    congr 1
    have huu : (↑u : ℂ) ≠ 0 := by simp only [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt hu
    push_cast
    field_simp
  rw [hfun, Measure.integral_comp_mul_left (fun η : ℝ => ψ η * czE (c / u) η) u]
  rw [abs_of_pos (inv_pos.mpr hu), Complex.real_smul]
  rfl

lemma czKern_czSymb (A : ℝ) (d : ℕ) (D : Finset ℝ) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (ψ : ℝ → ℂ)
    (hA : 0 < A) (hDpos : ∀ N ∈ D, 0 < N) (hψint : Integrable ψ) (hψmeas : Measurable ψ)
    (x : ℝ) :
    czKern (czSymb A d D lam eps ψ) x
      = ∑ N ∈ D, eps N * ((A * N ^ d)⁻¹
          * czPhi ψ ((lam N * (A * N ^ d) + x) / (A * N ^ d))) := by
  have hterm : ∀ N ∈ D, (∫ ξ : ℝ, (eps N * (ψ (A * N ^ d * ξ)
        * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))) * czE x ξ)
      = eps N * ((A * N ^ d)⁻¹
          * czPhi ψ ((lam N * (A * N ^ d) + x) / (A * N ^ d))) := by
    intro N hN
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    have hsplit : (∫ ξ : ℝ, (eps N * (ψ (A * N ^ d * ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))) * czE x ξ)
        = eps N * ∫ ξ : ℝ, (ψ (A * N ^ d * ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))) * czE x ξ := by
      rw [show (∫ ξ : ℝ, (eps N * (ψ (A * N ^ d * ξ)
            * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))) * czE x ξ)
          = ∫ ξ : ℝ, eps N * ((ψ (A * N ^ d * ξ)
            * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))) * czE x ξ) from by
        apply integral_congr_ae
        filter_upwards with ξ
        ring]
      rw [integral_const_mul]
    rw [hsplit]
    congr 1
    have hcomb : (∫ ξ : ℝ, (ψ (A * N ^ d * ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))) * czE x ξ)
        = ∫ ξ : ℝ, ψ ((A * N ^ d) * ξ) * czE (lam N * (A * N ^ d) + x) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [mul_assoc]
      have h1 : Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))
          = czE (lam N * (A * N ^ d)) ξ := by
        simp only [czE]
        congr 1
        push_cast
        ring
      rw [h1, ← czE_add]
    rw [hcomb, cz_int_term ψ (A * N ^ d) (lam N * (A * N ^ d) + x) hu]
  rw [czKern]
  simp only [czSymb]
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl hterm
  · intro N hN
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    have hcont : AEStronglyMeasurable (fun ξ : ℝ => (eps N * (ψ (A * N ^ d * ξ)
        * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))) * czE x ξ)
        (volume : Measure ℝ) := by
      refine AEStronglyMeasurable.mul ?_ (continuous_czE x).aestronglyMeasurable
      refine AEStronglyMeasurable.mul aestronglyMeasurable_const ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (hψmeas.comp (measurable_const_mul _)).aestronglyMeasurable
      · exact (by fun_prop : Continuous fun ξ : ℝ =>
            Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))).aestronglyMeasurable
    refine Integrable.mono' (g := fun ξ : ℝ => ‖eps N‖ * ‖ψ (A * N ^ d * ξ)‖) ?_ hcont ?_
    · exact (hψint.norm.comp_mul_left' (ne_of_gt hu)).const_mul ‖eps N‖
    · filter_upwards with ξ
      have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))‖ = 1 := by
        rw [show (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))
            = ((2 * Real.pi * (lam N * A * N ^ d * ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have hval : ‖(eps N * (ψ (A * N ^ d * ξ)
            * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))) * czE x ξ‖
          = ‖eps N‖ * ‖ψ (A * N ^ d * ξ)‖ := by
        rw [norm_mul, norm_czE, mul_one, norm_mul, norm_mul, hexp, mul_one]
      rw [hval]
/-- `czPhi` is the inverse Fourier transform of `ψ`. -/
lemma czPhi_eq_fourierInv (ψ : SchwartzMap ℝ ℂ) (t : ℝ) :
    czPhi (ψ : ℝ → ℂ) t = (𝓕⁻ ψ : SchwartzMap ℝ ℂ) t := by
  rw [czPhi, SchwartzMap.fourierInv_coe ψ, Real.fourierInv_eq_fourier_neg, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with η
  simp only [czE, smul_eq_mul]
  rw [mul_comm (ψ η)]
  congr 1
  rw [show (↑(-2 * Real.pi * inner ℝ η (-t)) : ℂ) * Complex.I
      = (2 : ℂ) * ↑Real.pi * Complex.I * (↑t * ↑η) by
    rw [inner_neg_right, Real.inner_apply]
    push_cast
    ring]

/-- The derivative of the real part of a complex-valued function. -/
lemma deriv_re_of_complex {f : ℝ → ℂ} {t : ℝ} (hd : DifferentiableAt ℝ f t) :
    deriv (fun s => (f s).re) t = (deriv f t).re := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ (deriv f t)) t :=
    hd.hasDerivAt.hasFDerivAt
  have h2 : HasFDerivAt (fun s => (f s).re)
      (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (deriv f t))) t :=
    (Complex.reCLM.hasFDerivAt (x := f t)).comp t h1
  have h3 : HasDerivAt (fun s => (f s).re) (deriv f t).re t := by
    have := h2.hasDerivAt
    simpa using this
  rw [h3.deriv]

/-- The derivative of the imaginary part of a complex-valued function. -/
lemma deriv_im_of_complex {f : ℝ → ℂ} {t : ℝ} (hd : DifferentiableAt ℝ f t) :
    deriv (fun s => (f s).im) t = (deriv f t).im := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ (deriv f t)) t :=
    hd.hasDerivAt.hasFDerivAt
  have h2 : HasFDerivAt (fun s => (f s).im)
      (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (deriv f t))) t :=
    (Complex.imCLM.hasFDerivAt (x := f t)).comp t h1
  have h3 : HasDerivAt (fun s => (f s).im) (deriv f t).im t := by
    have := h2.hasDerivAt
    simpa using this
  rw [h3.deriv]

/-- The real part of `czPhi ψ` satisfies the hypotheses of the shifted Calderón--Zygmund
kernel estimate, with the constants produced by `fourierInv_schwartz_decay`. -/
lemma czPhi_decay (C : ℝ) (hC : 0 < C) (ψ : SchwartzMap ℝ ℂ)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ / (1 + t ^ 2)) ∧
      (∀ t : ℝ, ‖deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t‖ ≤ C₁ / (1 + t ^ 2)) := by
  obtain ⟨C₁, hC₁, h1, h2⟩ :=
    Commons.Analysis.Schwartz.fourierInv_schwartz_decay C hC ψ hψsupp hψj
  refine ⟨C₁, hC₁, fun t => ?_, fun t => ?_⟩
  · rw [czPhi_eq_fourierInv]
    exact h1 t
  · have hid : deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t
        = deriv (fun s : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) s) t := by
      congr 1
      funext s
      exact czPhi_eq_fourierInv ψ s
    rw [hid]
    exact h2 t

/-- The real part of `czPhi ψ` is differentiable with the expected derivative bound. -/
lemma czPhi_re_deriv (C : ℝ) (hC : 0 < C) (ψ : SchwartzMap ℝ ℂ)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ t : ℝ, |(czPhi (ψ : ℝ → ℂ) t).re| ≤ C₁ / (1 + t ^ 2)) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re)
          (deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re) t) t) ∧
      (∀ t : ℝ, |deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re) t| ≤ C₁ / (1 + t ^ 2)) := by
  obtain ⟨C₁, hC₁, h1, h2⟩ := czPhi_decay C hC ψ hψsupp hψj
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t := by
    intro t
    have hid : (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        = fun s : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) s := by
      funext s
      exact czPhi_eq_fourierInv ψ s
    rw [hid]
    exact (SchwartzMap.differentiable (𝓕⁻ ψ)) t
  refine ⟨C₁, hC₁, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · exact (Complex.abs_re_le_norm _).trans (h1 t)
  · have h1' := (hdiff t).hasDerivAt
    have h1'' : HasFDerivAt (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t)) t :=
      h1'.hasFDerivAt
    have h2'' : HasFDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re)
        (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t))) t :=
      (Complex.reCLM.hasFDerivAt (x := czPhi (ψ : ℝ → ℂ) t)).comp t h1''
    have h3'' : HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re)
        (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t).re t := by
      have := h2''.hasDerivAt
      simpa using this
    rwa [h3''.deriv]
  · rw [deriv_re_of_complex (hdiff t)]
    exact (Complex.abs_re_le_norm _).trans (h2 t)

/-- Same for the imaginary part. -/
lemma czPhi_im_deriv (C : ℝ) (hC : 0 < C) (ψ : SchwartzMap ℝ ℂ)
    (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
    (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ t : ℝ, |(czPhi (ψ : ℝ → ℂ) t).im| ≤ C₁ / (1 + t ^ 2)) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im)
          (deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im) t) t) ∧
      (∀ t : ℝ, |deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im) t| ≤ C₁ / (1 + t ^ 2)) := by
  obtain ⟨C₁, hC₁, h1, h2⟩ := czPhi_decay C hC ψ hψsupp hψj
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t := by
    intro t
    have hid : (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        = fun s : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) s := by
      funext s
      exact czPhi_eq_fourierInv ψ s
    rw [hid]
    exact (SchwartzMap.differentiable (𝓕⁻ ψ)) t
  refine ⟨C₁, hC₁, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · exact (Complex.abs_im_le_norm _).trans (h1 t)
  · have h1' := (hdiff t).hasDerivAt
    have h1'' : HasFDerivAt (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t)) t :=
      h1'.hasFDerivAt
    have h2'' : HasFDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im)
        (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t))) t :=
      (Complex.imCLM.hasFDerivAt (x := czPhi (ψ : ℝ → ℂ) t)).comp t h1''
    have h3'' : HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im)
        (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t).im t := by
      have := h2''.hasDerivAt
      simpa using this
    rwa [h3''.deriv]
  · rw [deriv_im_of_complex (hdiff t)]
    exact (Complex.abs_im_le_norm _).trans (h2 t)


/-- Integrability of the affine rescaling of `(1 + x²)⁻¹`. -/
lemma integrable_inv_one_add_sq_affine (u c : ℝ) (hu : 0 < u) :
    Integrable (fun x : ℝ => (1 + ((x - c) / u) ^ 2)⁻¹) := by
  have h1 : Integrable (fun s : ℝ => (1 + s ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun s : ℝ => (1 + (s * u⁻¹) ^ 2)⁻¹) :=
    h1.comp_mul_right' (inv_ne_zero (ne_of_gt hu))
  simpa [div_eq_mul_inv] using h2.comp_sub_right c

/-- Integrability of `(1 + ((x + c)/u)²)⁻¹`. -/
lemma integrable_inv_one_add_sq_add (u c : ℝ) (hu : 0 < u) :
    Integrable (fun x : ℝ => (1 + ((x + c) / u) ^ 2)⁻¹) := by
  have h : Integrable (fun x : ℝ => (1 + ((x - -c) / u) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq_affine u (-c) hu
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [show (x - -c) / u = (x + c) / u by ring]

/-- Integrability of `(1 + ((x - c - y)/u)²)⁻¹`. -/
lemma integrable_inv_one_add_sq_sub_sub (u c y : ℝ) (hu : 0 < u) :
    Integrable (fun x : ℝ => (1 + ((x - c - y) / u) ^ 2)⁻¹) := by
  have h := integrable_inv_one_add_sq_affine u (c + y) hu
  refine h.congr ?_
  filter_upwards with x
  congr 2
  ring

/-- Pointwise bound for one summand of the kernel estimate. -/
lemma kernel_term_bound (u : ℝ) (hu : 0 < u) (e z w : ℂ) (he : ‖e‖ ≤ 1) :
    ‖e * (u⁻¹ * z) - e * (u⁻¹ * w)‖ ≤ (1 / u) * |z.re - w.re| + (1 / u) * |z.im - w.im| := by
  have h1 : e * (u⁻¹ * z) - e * (u⁻¹ * w) = e * (u⁻¹ * (z - w)) := by ring
  rw [h1, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu)]
  have h3 : u⁻¹ * ‖z - w‖ ≤ u⁻¹ * (|z.re - w.re| + |z.im - w.im|) :=
    mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im _) (by positivity)
  have h2 : ‖e‖ * (u⁻¹ * ‖z - w‖) ≤ (1 / u) * (|z.re - w.re| + |z.im - w.im|) := by
    calc ‖e‖ * (u⁻¹ * ‖z - w‖) ≤ 1 * (u⁻¹ * ‖z - w‖) :=
          mul_le_mul_of_nonneg_right he (by positivity)
      _ ≤ 1 * (u⁻¹ * (|z.re - w.re| + |z.im - w.im|)) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = (1 / u) * (|z.re - w.re| + |z.im - w.im|) := by rw [one_mul, inv_eq_one_div]
  rw [mul_add] at h2
  exact h2

/-- The shifted Calderón--Zygmund kernel estimate for the kernels
`ε_N u_N⁻¹ Φ((· + λ_N u_N)/u_N)`. -/
lemma cz_kernel_sum_le (C Λ A : ℝ) (hC : 0 < C) (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (hA : 0 < A) :
    ∃ C', 0 < C' ∧ ∀ (Kc : ℝ) (hKc : 1 ≤ Kc) (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N)
      (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
      (lam : ℝ → ℝ) (hlam : ∀ N ∈ D, |lam N| ≤ 2 ^ Kc)
      (ψ : SchwartzMap ℝ ℂ) (hψ0 : ψ 0 = 0)
      (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
      (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C)
      (eps : ℝ → ℂ) (heps : ∀ N ∈ D, ‖eps N‖ ≤ 1)
      (L : ℝ) (hL : 0 < L) (y : ℝ) (hy : |y| ≤ L / 2),
      (∑ N ∈ D, ∫ x in {x : ℝ | 50 * L ≤ |x|},
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖)
        ≤ C' * Kc := by
  obtain ⟨C₁, hC₁, hdec⟩ :=
    Commons.Analysis.Schwartz.fourierInv_schwartz_decay_controlled C hC
  obtain ⟨C₂, hC₂, hle⟩ := lacunary_shifted_kernel_sum_le C₁ hC₁ Λ hΛ A hA d hd
  refine ⟨2 * C₂, by positivity, ?_⟩
  intro Kc hKc D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps L hL y hy
  have hΦ : ∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ / (1 + t ^ 2) := by
    intro t
    rw [czPhi_eq_fourierInv]
    exact (hdec ψ hψ0 hψsupp hψj t).1
  have hΦ' : ∀ t : ℝ, ‖deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t‖ ≤ C₁ / (1 + t ^ 2) := by
    intro t
    have hid : deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t
        = deriv (fun s : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) s) t := by
      congr 1
      funext s
      exact czPhi_eq_fourierInv ψ s
    rw [hid]
    exact (hdec ψ hψ0 hψsupp hψj t).2
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t := by
    intro t
    have hid : (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        = fun s : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) s := by
      funext s
      exact czPhi_eq_fourierInv ψ s
    rw [hid]
    exact (SchwartzMap.differentiable (𝓕⁻ ψ)) t
  have hΦcont : Continuous fun t : ℝ => czPhi (ψ : ℝ → ℂ) t := by
    have hid : (fun t : ℝ => czPhi (ψ : ℝ → ℂ) t)
        = fun t : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) t := funext fun t => czPhi_eq_fourierInv ψ t
    rw [hid]
    exact (SchwartzMap.differentiable (𝓕⁻ ψ)).continuous
  have hRe1 : ∀ t : ℝ, |(czPhi (ψ : ℝ → ℂ) t).re| ≤ C₁ / (1 + t ^ 2) :=
    fun t => (Complex.abs_re_le_norm _).trans (hΦ t)
  have hRe2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re)
      (deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re) t) t := by
    intro t
    have h1' := (hdiff t).hasDerivAt
    have h1'' : HasFDerivAt (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        (ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t)) t := h1'.hasFDerivAt
    have h2'' : HasFDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re)
        (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t))) t :=
      (Complex.reCLM.hasFDerivAt (x := czPhi (ψ : ℝ → ℂ) t)).comp t h1''
    have h3'' : HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re)
        (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t).re t := by
      have := h2''.hasDerivAt
      simpa using this
    rwa [h3''.deriv]
  have hRe3 : ∀ t : ℝ, |deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).re) t|
      ≤ C₁ / (1 + t ^ 2) := by
    intro t
    rw [deriv_re_of_complex (hdiff t)]
    exact (Complex.abs_re_le_norm _).trans (hΦ' t)
  have hIm1 : ∀ t : ℝ, |(czPhi (ψ : ℝ → ℂ) t).im| ≤ C₁ / (1 + t ^ 2) :=
    fun t => (Complex.abs_im_le_norm _).trans (hΦ t)
  have hIm2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im)
      (deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im) t) t := by
    intro t
    have h1' := (hdiff t).hasDerivAt
    have h1'' : HasFDerivAt (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s)
        (ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t)) t := h1'.hasFDerivAt
    have h2'' : HasFDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im)
        (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ
          (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t))) t :=
      (Complex.imCLM.hasFDerivAt (x := czPhi (ψ : ℝ → ℂ) t)).comp t h1''
    have h3'' : HasDerivAt (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im)
        (deriv (fun s : ℝ => czPhi (ψ : ℝ → ℂ) s) t).im t := by
      have := h2''.hasDerivAt
      simpa using this
    rwa [h3''.deriv]
  have hIm3 : ∀ t : ℝ, |deriv (fun s : ℝ => (czPhi (ψ : ℝ → ℂ) s).im) t|
      ≤ C₁ / (1 + t ^ 2) := by
    intro t
    rw [deriv_im_of_complex (hdiff t)]
    exact (Complex.abs_im_le_norm _).trans (hΦ' t)
  have hR := hle Kc L hKc hL D hDpos hlac (fun N => -lam N)
    (fun N hN => by rw [abs_neg]; exact hlam N hN)
    (fun t => (czPhi (ψ : ℝ → ℂ) t).re) hRe1 hRe2 hRe3 y hy
  have hI := hle Kc L hKc hL D hDpos hlac (fun N => -lam N)
    (fun N hN => by rw [abs_neg]; exact hlam N hN)
    (fun t => (czPhi (ψ : ℝ → ℂ) t).im) hIm1 hIm2 hIm3 y hy
  -- pointwise bound for each summand
  have hpt : ∀ N ∈ D, ∀ x : ℝ,
      ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
        - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
            ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖
      ≤ (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
            - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|
        + (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
            - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im| := by
    intro N hN x
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    rw [show (lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)
          = (x - -lam N * A * N ^ d - y) / (A * N ^ d) by ring,
      show (lam N * (A * N ^ d) + x) / (A * N ^ d)
          = (x - -lam N * A * N ^ d) / (A * N ^ d) by ring]
    exact kernel_term_bound (A * N ^ d) hu (eps N) _ _ (heps N hN)
  -- integrability of the two pieces of each summand
  have hIntRe : ∀ N ∈ D, Integrable (fun x : ℝ =>
      (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
        - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|) := by
    intro N hN
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    have hcont : Continuous fun x : ℝ =>
        (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
          - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re| := by
      have h1 : Continuous fun x : ℝ =>
          (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re :=
        Complex.continuous_re.comp (hΦcont.comp (by fun_prop))
      have h2 : Continuous fun x : ℝ =>
          (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re :=
        Complex.continuous_re.comp (hΦcont.comp (by fun_prop))
      exact continuous_const.mul ((h1.sub h2).abs)
    have hdom : Integrable (fun x : ℝ => (1 / (A * N ^ d)) *
        (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
          + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.add ?_ ?_
      · exact (integrable_inv_one_add_sq_sub_sub (A * N ^ d) (-lam N * A * N ^ d) y hu).const_mul C₁
      · exact (integrable_inv_one_add_sq_affine (A * N ^ d) (-lam N * A * N ^ d) hu).const_mul C₁
    refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 := hRe1 ((x - -lam N * A * N ^ d - y) / (A * N ^ d))
    have h2 := hRe1 ((x - -lam N * A * N ^ d) / (A * N ^ d))
    have h3 : |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
        - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|
        ≤ C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
          + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹ := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rwa [div_eq_mul_inv] at h1 ⊢
      · rwa [div_eq_mul_inv] at h2 ⊢
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (A * N ^ d)),
      Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hIntIm : ∀ N ∈ D, Integrable (fun x : ℝ =>
      (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
        - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im|) := by
    intro N hN
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    have hcont : Continuous fun x : ℝ =>
        (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
          - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im| := by
      have h1 : Continuous fun x : ℝ =>
          (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im :=
        Complex.continuous_im.comp (hΦcont.comp (by fun_prop))
      have h2 : Continuous fun x : ℝ =>
          (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im :=
        Complex.continuous_im.comp (hΦcont.comp (by fun_prop))
      exact continuous_const.mul ((h1.sub h2).abs)
    have hdom : Integrable (fun x : ℝ => (1 / (A * N ^ d)) *
        (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
          + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.add ?_ ?_
      · exact (integrable_inv_one_add_sq_sub_sub (A * N ^ d) (-lam N * A * N ^ d) y hu).const_mul C₁
      · exact (integrable_inv_one_add_sq_affine (A * N ^ d) (-lam N * A * N ^ d) hu).const_mul C₁
    refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    filter_upwards with x
    have h1 := hIm1 ((x - -lam N * A * N ^ d - y) / (A * N ^ d))
    have h2 := hIm1 ((x - -lam N * A * N ^ d) / (A * N ^ d))
    have h3 : |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
        - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im|
        ≤ C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
          + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹ := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rwa [div_eq_mul_inv] at h1 ⊢
      · rwa [div_eq_mul_inv] at h2 ⊢
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (A * N ^ d)),
      Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  -- combine
  have hsum : (∑ N ∈ D, ∫ x in {x : ℝ | 50 * L ≤ |x|},
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖)
      ≤ (∑ N ∈ D, ∫ x in {x : ℝ | 50 * L ≤ |x|},
          (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
            - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|)
        + (∑ N ∈ D, ∫ x in {x : ℝ | 50 * L ≤ |x|},
          (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
            - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro N hN
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    have hB : Integrable (fun x : ℝ =>
        C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
        + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹) := by
      refine Integrable.add ?_ ?_
      · exact (integrable_inv_one_add_sq_sub_sub (A * N ^ d) (-lam N * A * N ^ d) y hu).const_mul C₁
      · exact (integrable_inv_one_add_sq_affine (A * N ^ d) (-lam N * A * N ^ d) hu).const_mul C₁
    have hdom : Integrable (fun x : ℝ => (1 / (A * N ^ d)) *
        ((C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
          + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)
        + (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
          + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹))) :=
      (hB.add hB).const_mul _
    have hbound : ∀ x : ℝ,
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖
        ≤ (1 / (A * N ^ d)) *
          ((C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
            + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)
          + (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
            + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)) := by
      intro x
      have h1 := hRe1 ((x - -lam N * A * N ^ d - y) / (A * N ^ d))
      have h2 := hRe1 ((x - -lam N * A * N ^ d) / (A * N ^ d))
      have h3 := hIm1 ((x - -lam N * A * N ^ d - y) / (A * N ^ d))
      have h4 := hIm1 ((x - -lam N * A * N ^ d) / (A * N ^ d))
      have h5 : |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
            - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|
          ≤ C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
            + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹ := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rwa [div_eq_mul_inv] at h1 ⊢
        · rwa [div_eq_mul_inv] at h2 ⊢
      have h6 : |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
            - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im|
          ≤ C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
            + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹ := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rwa [div_eq_mul_inv] at h3 ⊢
        · rwa [div_eq_mul_inv] at h4 ⊢
      calc ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
            - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
                ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖
          ≤ (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
              - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|
            + (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
              - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im| := hpt N hN x
        _ ≤ (1 / (A * N ^ d)) *
              (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
                + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)
            + (1 / (A * N ^ d)) *
              (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
                + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹) :=
            add_le_add (mul_le_mul_of_nonneg_left h5 (by positivity))
              (mul_le_mul_of_nonneg_left h6 (by positivity))
        _ = (1 / (A * N ^ d)) *
              ((C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
                + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)
              + (C₁ * (1 + ((x - -lam N * A * N ^ d - y) / (A * N ^ d)) ^ 2)⁻¹
                + C₁ * (1 + ((x - -lam N * A * N ^ d) / (A * N ^ d)) ^ 2)⁻¹)) := by ring
    have hterm_int : Integrable (fun x : ℝ =>
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖) :=
      Integrable.mono' ((hIntRe N hN).add (hIntIm N hN))
        (Continuous.aestronglyMeasurable (by
          refine Continuous.norm ?_
          refine Continuous.sub ?_ ?_
          · exact continuous_const.mul (continuous_const.mul (hΦcont.comp (by fun_prop)))
          · exact continuous_const.mul (continuous_const.mul (hΦcont.comp (by fun_prop)))))
        (Filter.Eventually.of_forall (fun x => by simpa using hpt N hN x))
    calc ∫ x in {x : ℝ | 50 * L ≤ |x|},
          ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
            - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
                ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖
        ≤ ∫ x in {x : ℝ | 50 * L ≤ |x|},
          ((1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
              - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|
            + (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
              - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im|) :=
          integral_mono_ae hterm_int.integrableOn
            ((hIntRe N hN).add (hIntIm N hN)).integrableOn
            (Filter.Eventually.of_forall (fun x => hpt N hN x))
      _ = (∫ x in {x : ℝ | 50 * L ≤ |x|},
            (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).re
              - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).re|)
          + (∫ x in {x : ℝ | 50 * L ≤ |x|},
            (1 / (A * N ^ d)) * |(czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d - y) / (A * N ^ d))).im
              - (czPhi (ψ : ℝ → ℂ) ((x - -lam N * A * N ^ d) / (A * N ^ d))).im|) :=
          integral_add (hIntRe N hN).integrableOn (hIntIm N hN).integrableOn
  -- final assembly
  have hsum2 : (∑ N ∈ D, ∫ x in {x : ℝ | 50 * L ≤ |x|},
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖) ≤ 2 * C₂ * Kc := by
    refine hsum.trans ?_
    have hfin : C₂ * Kc + C₂ * Kc ≤ 2 * C₂ * Kc := by linarith
    exact (add_le_add hR hI).trans hfin
  exact hsum2


/-! ## Integrability of the symbol and of the individual kernel terms -/

lemma continuous_czPhi (ψ : SchwartzMap ℝ ℂ) :
    Continuous fun t : ℝ => czPhi (ψ : ℝ → ℂ) t := by
  have hid : (fun t : ℝ => czPhi (ψ : ℝ → ℂ) t)
      = fun t : ℝ => (𝓕⁻ ψ : SchwartzMap ℝ ℂ) t :=
    funext fun t => czPhi_eq_fourierInv ψ t
  rw [hid]
  exact (SchwartzMap.differentiable (𝓕⁻ ψ)).continuous

/-- The symbol of the shifted Calderón--Zygmund multiplier is integrable. -/
lemma czSymb_integrable (A : ℝ) (hA : 0 < A) (d : ℕ) (D : Finset ℝ)
    (hDpos : ∀ N ∈ D, 0 < N) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) :
    Integrable (czSymb A d D lam eps (ψ : ℝ → ℂ)) := by
  rw [show czSymb A d D lam eps (ψ : ℝ → ℂ) = fun ξ : ℝ => ∑ N ∈ D, eps N * (ψ (A * N ^ d * ξ)
      * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))) from rfl]
  refine integrable_finsetSum D (fun N hN => ?_)
  have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
  refine Integrable.mono'
    (f := fun ξ : ℝ => eps N * (ψ (A * N ^ d * ξ)
      * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))))
    (g := fun ξ : ℝ => ‖eps N‖ * ‖ψ (A * N ^ d * ξ)‖)
    ((ψ.integrable.norm.comp_mul_left' (ne_of_gt hu)).const_mul ‖eps N‖) ?_ ?_
  · exact Continuous.aestronglyMeasurable (by
      refine Continuous.mul continuous_const (Continuous.mul ?_ ?_)
      · exact ψ.continuous.comp (by fun_prop)
      · exact Complex.continuous_exp.comp (by fun_prop))
  · filter_upwards with ξ
    have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))‖ = 1 := by
      rw [show (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))
          = ((2 * Real.pi * (lam N * A * N ^ d * ξ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, norm_mul, hexp, mul_one]

/-- Integrability of a constant multiple of an affine rescaling of `czPhi`, in the exact
shape needed for the individual kernel terms. -/
lemma integrable_czPhi_shift (φ : ℝ → ℂ) (hcont : Continuous (czPhi φ)) (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hΦ : ∀ t : ℝ, ‖czPhi φ t‖ ≤ C₁ * (1 + t ^ 2)⁻¹)
    (E : ℂ) (k u a y : ℝ) (hu : 0 < u) :
    Integrable (fun x : ℝ => E * ((k : ℂ) * czPhi φ ((a + (x - y)) / u))) := by
  have hdom : Integrable (fun x : ℝ => ‖E‖ * |k| * C₁ * (1 + ((x + (a - y)) / u) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq_add u (a - y) hu).const_mul (‖E‖ * |k| * C₁)
  refine Integrable.mono'
    (f := fun x : ℝ => E * ((k : ℂ) * czPhi φ ((a + (x - y)) / u)))
    (g := fun x : ℝ => ‖E‖ * |k| * C₁ * (1 + ((x + (a - y)) / u) ^ 2)⁻¹) hdom ?_ ?_
  · exact Continuous.aestronglyMeasurable (by
      refine Continuous.mul continuous_const (Continuous.mul continuous_const ?_)
      exact hcont.comp (by fun_prop))
  · filter_upwards with x
    have harg : (a + (x - y)) / u = (x + (a - y)) / u := by ring
    calc ‖E * ((k : ℂ) * czPhi φ ((a + (x - y)) / u))‖
        = ‖E‖ * (|k| * ‖czPhi φ ((x + (a - y)) / u)‖) := by
          rw [norm_mul, norm_mul, harg, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖E‖ * (|k| * (C₁ * (1 + ((x + (a - y)) / u) ^ 2)⁻¹)) := by
          gcongr
          exact hΦ _
      _ = ‖E‖ * |k| * C₁ * (1 + ((x + (a - y)) / u) ^ 2)⁻¹ := by ring

/-- Each summand of the Calderón--Zygmund kernel difference is integrable. -/
lemma cz_kernel_term_integrable (A : ℝ) (hA : 0 < A) (d : ℕ) (D : Finset ℝ)
    (hDpos : ∀ N ∈ D, 0 < N) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hΦ : ∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ * (1 + t ^ 2)⁻¹)
    (y : ℝ) (N : ℝ) (hN : N ∈ D) :
    Integrable (fun x : ℝ =>
      eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
        - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
            ((lam N * (A * N ^ d) + x) / (A * N ^ d)))) := by
  have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
  have h1 : Integrable (fun x : ℝ => eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
      ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))) :=
    integrable_czPhi_shift (ψ : ℝ → ℂ) (continuous_czPhi ψ) C₁ (le_of_lt hC₁) hΦ
      (eps N) ((A * N ^ d)⁻¹) (A * N ^ d) (lam N * (A * N ^ d)) y hu
  have h2 : Integrable (fun x : ℝ => eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
      ((lam N * (A * N ^ d) + x) / (A * N ^ d)))) := by
    simpa [sub_zero] using
      (integrable_czPhi_shift (ψ : ℝ → ℂ) (continuous_czPhi ψ) C₁ (le_of_lt hC₁) hΦ
        (eps N) ((A * N ^ d)⁻¹) (A * N ^ d) (lam N * (A * N ^ d)) 0 hu)
  exact h1.sub h2

/-- The shifted Calderón--Zygmund kernel estimate, in lintegral form: the hypothesis needed by
`cz_weak_type_one_lintegral`. -/
lemma cz_kernel_sum_le_lintegral (C Λ A : ℝ) (hC : 0 < C) (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d)
    (hA : 0 < A) :
    ∃ C', 0 < C' ∧ ∀ (Kc : ℝ) (hKc : 1 ≤ Kc) (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N)
      (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
      (lam : ℝ → ℝ) (hlam : ∀ N ∈ D, |lam N| ≤ 2 ^ Kc)
      (ψ : SchwartzMap ℝ ℂ) (hψ0 : ψ 0 = 0)
      (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
      (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C)
      (eps : ℝ → ℂ) (heps : ∀ N ∈ D, ‖eps N‖ ≤ 1)
      (L : ℝ) (hL : 0 < L) (y : ℝ) (hy : |y| ≤ L / 2),
      (∑ N ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖ₑ)
        ≤ ENNReal.ofReal (C' * Kc) := by
  obtain ⟨Ck, hCk, hboom⟩ := cz_kernel_sum_le C Λ A hC hΛ d hd hA
  refine ⟨Ck, hCk, ?_⟩
  intro Kc hKc D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps L hL y hy
  obtain ⟨C₁, hC₁, hdec1, _⟩ :=
    Commons.Analysis.Schwartz.fourierInv_schwartz_decay C hC ψ hψsupp hψj
  have hPhi : ∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ * (1 + t ^ 2)⁻¹ := by
    intro t
    rw [czPhi_eq_fourierInv]
    simpa [div_eq_mul_inv] using hdec1 t
  have hterm : ∀ N ∈ D, IntegrableOn (fun x : ℝ =>
      eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
        - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
            ((lam N * (A * N ^ d) + x) / (A * N ^ d)))) {x : ℝ | 50 * L ≤ |x|} :=
    fun N hN => (cz_kernel_term_integrable A hA d D hDpos lam eps ψ C₁ hC₁ hPhi y N hN).integrableOn
  have h3 := Commons.Analysis.Measure.finset_lintegral_enorm_le_ofReal_sum D (fun N x =>
      eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
        - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
            ((lam N * (A * N ^ d) + x) / (A * N ^ d)))) {x : ℝ | 50 * L ≤ |x|} hterm
  refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
  exact hboom Kc hKc D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps L hL y hy

/-- The kernel of the conjugate symbol. -/
def czKernConj (m : ℝ → ℂ) : ℝ → ℂ := czKern (fun ξ => (starRingEnd ℂ) (m ξ))

/-- Conjugation of the exponential character. -/
lemma star_czE (x ξ : ℝ) : (starRingEnd ℂ) (czE x ξ) = czE (-x) ξ := by
  rw [czE, czE,
    show (2:ℂ) * ↑Real.pi * Complex.I * (↑x * ↑ξ) = ↑(2 * Real.pi * (x * ξ)) * Complex.I by
      push_cast; ring,
    show (2:ℂ) * ↑Real.pi * Complex.I * (↑(-x) * ↑ξ) = ↑(2 * Real.pi * (-x * ξ)) * Complex.I by
      push_cast; ring]
  refine Complex.ext ?_ ?_
  · rw [Complex.conj_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re,
      show 2 * Real.pi * (-x * ξ) = -(2 * Real.pi * (x * ξ)) from by ring, Real.cos_neg]
  · rw [Complex.conj_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
      show 2 * Real.pi * (-x * ξ) = -(2 * Real.pi * (x * ξ)) from by ring, Real.sin_neg]

/-- The kernel of the conjugate symbol is the conjugate-reflected kernel. -/
lemma czKern_conj (m : ℝ → ℂ) (hm : Integrable m) :
    czKern (fun ξ => (starRingEnd ℂ) (m ξ)) = fun t => (starRingEnd ℂ) (czKern m (-t)) := by
  funext t
  rw [czKern, czKern]
  have hint : Integrable (fun ξ : ℝ => m ξ * czE (-t) ξ) := by
    refine Integrable.mono' (hm.norm) ?_ ?_
    · exact hm.aestronglyMeasurable.mul (continuous_czE (-t)).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul, norm_czE, mul_one]
  have h := ContinuousLinearMap.integral_comp_comm
    ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) hint
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [map_mul, star_czE, neg_neg]

/-! ## The kernel of the shifted symbol: boundedness, measurability, smoothness -/

lemma czKern_czSymb_bounded (A : ℝ) (hA : 0 < A) (d : ℕ) (D : Finset ℝ)
    (hDpos : ∀ N ∈ D, 0 < N) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (heps : ∀ N ∈ D, ‖eps N‖ ≤ 1)
    (ψ : SchwartzMap ℝ ℂ) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hΦ : ∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ * (1 + t ^ 2)⁻¹) :
    ∀ z : ℝ, ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) z‖
      ≤ ∑ N ∈ D, C₁ * (A * N ^ d)⁻¹ := by
  intro z
  rw [czKern_czSymb A d D lam eps (ψ : ℝ → ℂ) hA hDpos ψ.integrable ψ.continuous.measurable z]
  have hterm : ∀ N ∈ D,
      ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d)))‖
        ≤ C₁ * (A * N ^ d)⁻¹ := by
    intro N hN
    have hu : (0:ℝ) < A * N ^ d := mul_pos hA (pow_pos (hDpos N hN) d)
    have h1 : ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d)))‖
        = ‖eps N‖ * ((A * N ^ d)⁻¹ * ‖czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d))‖) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu)]
    rw [h1]
    have h2 : ‖czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d))‖ ≤ C₁ := by
      refine (hΦ _).trans ?_
      have h3 : (1 + ((lam N * (A * N ^ d) + z) / (A * N ^ d)) ^ 2)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by linarith [sq_nonneg ((lam N * (A * N ^ d) + z) / (A * N ^ d))])
      calc C₁ * (1 + ((lam N * (A * N ^ d) + z) / (A * N ^ d)) ^ 2)⁻¹
          ≤ C₁ * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hC₁)
        _ = C₁ := mul_one C₁
    calc ‖eps N‖ * ((A * N ^ d)⁻¹ * ‖czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d))‖)
        ≤ 1 * ((A * N ^ d)⁻¹ * C₁) :=
          mul_le_mul (heps N hN) (mul_le_mul_of_nonneg_left h2 (by positivity))
            (by positivity) (by norm_num)
      _ = C₁ * (A * N ^ d)⁻¹ := by ring
  calc ‖∑ N ∈ D, eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d)))‖
      ≤ ∑ N ∈ D, ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + z) / (A * N ^ d)))‖ :=
        norm_sum_le D _
    _ ≤ ∑ N ∈ D, C₁ * (A * N ^ d)⁻¹ := Finset.sum_le_sum hterm

lemma czKern_czSymb_measurable (A : ℝ) (hA : 0 < A) (d : ℕ) (D : Finset ℝ)
    (hDpos : ∀ N ∈ D, 0 < N) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) :
    Measurable (czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))) := by
  have hfun : czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))
      = fun z : ℝ => ∑ N ∈ D, eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
          ((lam N * (A * N ^ d) + z) / (A * N ^ d))) :=
    funext fun z => czKern_czSymb A d D lam eps (ψ : ℝ → ℂ) hA hDpos ψ.integrable
      ψ.continuous.measurable z
  rw [hfun]
  refine Finset.measurable_sum D (fun N _hN => ?_)
  refine Measurable.mul measurable_const (Measurable.mul measurable_const ?_)
  exact (continuous_czPhi ψ).measurable.comp (by fun_prop)

/-- The lintegral smoothness estimate for the combined kernel, deduced from the sum of the
individual estimates. -/
lemma czKern_diff_lintegral_le (A : ℝ) (hA : 0 < A) (d : ℕ) (D : Finset ℝ)
    (hDpos : ∀ N ∈ D, 0 < N) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (L y Aker : ℝ)
    (hsum : (∑ N ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖ₑ) ≤ ENNReal.ofReal Aker) :
    (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) (x - y)
          - czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) x‖ₑ) ≤ ENNReal.ofReal Aker := by
  have hpt : ∀ x : ℝ,
      ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) (x - y)
        - czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) x‖ₑ
      ≤ ∑ N ∈ D, ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
            ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
          - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖ₑ := by
    intro x
    rw [czKern_czSymb A d D lam eps (ψ : ℝ → ℂ) hA hDpos ψ.integrable ψ.continuous.measurable
        (x - y),
      czKern_czSymb A d D lam eps (ψ : ℝ → ℂ) hA hDpos ψ.integrable ψ.continuous.measurable x,
      ← Finset.sum_sub_distrib]
    exact enorm_sum_le D _
  have hmeas : ∀ N ∈ D, Measurable (fun x : ℝ =>
      ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ) ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
        - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
            ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖ₑ) := by
    intro N _hN
    have h1 : Measurable (fun x : ℝ => eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
        ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))) :=
      measurable_const.mul (measurable_const.mul ((continuous_czPhi ψ).measurable.comp (by fun_prop)))
    have h2 : Measurable (fun x : ℝ => eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
        ((lam N * (A * N ^ d) + x) / (A * N ^ d)))) :=
      measurable_const.mul (measurable_const.mul ((continuous_czPhi ψ).measurable.comp (by fun_prop)))
    exact (h1.sub h2).enorm
  calc (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) (x - y)
          - czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) x‖ₑ)
      ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ∑ N ∈ D, ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
            - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
                ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖ₑ :=
        lintegral_mono_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ N ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ‖eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
              ((lam N * (A * N ^ d) + (x - y)) / (A * N ^ d)))
            - eps N * ((A * N ^ d)⁻¹ * czPhi (ψ : ℝ → ℂ)
                ((lam N * (A * N ^ d) + x) / (A * N ^ d)))‖ₑ :=
        lintegral_finsetSum D hmeas
    _ ≤ ENNReal.ofReal Aker := hsum

/-- Reflection invariance of the whole-space lintegral. -/
lemma lintegral_comp_neg (g : ℝ → ℝ≥0∞) :
    (∫⁻ x, g (-x) ∂(volume : Measure ℝ)) = ∫⁻ x, g x := by
  have hmap : Measure.map (⇑(MeasurableEquiv.neg ℝ)) (volume : Measure ℝ) = volume := by
    rw [show (⇑(MeasurableEquiv.neg ℝ)) = (fun x : ℝ => -x) from rfl, Measure.map_neg_eq_self]
  have h := MeasureTheory.lintegral_map_equiv (μ := (volume : Measure ℝ)) (f := g)
    (MeasurableEquiv.neg ℝ)
  rw [hmap] at h
  exact h.symm

/-- Reflection invariance of a set-lintegral over a symmetric set. -/
lemma lintegral_set_comp_neg (F : ℝ → ℝ≥0∞) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : ∀ x : ℝ, x ∈ S ↔ -x ∈ S) :
    (∫⁻ x in S, F (-x)) = ∫⁻ x in S, F x := by
  calc (∫⁻ x in S, F (-x))
      = ∫⁻ x, S.indicator (fun y => F (-y)) x :=
        (MeasureTheory.lintegral_indicator hSm _).symm
    _ = ∫⁻ x, (S.indicator F) (-x) := by
        have hfun : (fun x => S.indicator (fun y => F (-y)) x) = fun x => (S.indicator F) (-x) := by
          funext x
          by_cases hx : x ∈ S
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hS x).mp hx)]
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hS x).mpr h))]
        rw [hfun]
    _ = ∫⁻ x, S.indicator F x := lintegral_comp_neg (S.indicator F)
    _ = ∫⁻ x in S, F x := MeasureTheory.lintegral_indicator hSm F

/-- `enorm` is invariant under complex conjugation. -/
lemma enorm_star (z : ℂ) : ‖(starRingEnd ℂ) z‖ₑ = ‖z‖ₑ := by
  rw [Commons.Analysis.CalderonZygmund.enorm_eq_ofReal_norm',
    Commons.Analysis.CalderonZygmund.enorm_eq_ofReal_norm', Complex.norm_conj]

/-- The kernel of the conjugate symbol satisfies the same smoothness estimate. -/
lemma czKern_conj_hker (m : ℝ → ℂ) (hm : Integrable m) (Aker : ℝ)
    (hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      (∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖czKern m (x - y) - czKern m x‖ₑ)
        ≤ ENNReal.ofReal Aker) :
    ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ‖czKernConj m (x - y)
            - czKernConj m x‖ₑ) ≤ ENNReal.ofReal Aker := by
  intro L hL y hy
  have hpt : ∀ x : ℝ,
      ‖czKernConj m (x - y) - czKernConj m x‖ₑ
        = ‖czKern m ((-x) - (-y)) - czKern m (-x)‖ₑ := by
    intro x
    rw [czKernConj, czKern_conj m hm]
    dsimp only
    rw [show -(x - y) = -x + y by ring, show -x - -y = -x + y by ring,
      ← map_sub, enorm_star]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [lintegral_set_comp_neg (fun t => ‖czKern m (t - (-y)) - czKern m t‖ₑ)
    (measurableSet_le measurable_const continuous_abs.measurable)
    (fun x => by simp only [Set.mem_setOf_eq, abs_neg])]
  exact hker L hL (-y) (by rwa [abs_neg])

/-! ## Abstract `L^p` bounds for the Calderón--Zygmund multiplier -/

lemma integrable_star_comp (m : ℝ → ℂ) (hm : Integrable m) :
    Integrable (fun ξ : ℝ => (starRingEnd ℂ) (m ξ)) := by
  refine Integrable.mono' (f := fun ξ : ℝ => (starRingEnd ℂ) (m ξ))
    (g := fun ξ : ℝ => ‖m ξ‖) hm.norm ?_ ?_
  · exact continuous_star.comp_aestronglyMeasurable hm.aestronglyMeasurable
  · filter_upwards with ξ
    rw [Complex.norm_conj]

/-- A convolution operator with a bounded kernel is bounded by `Bk * ‖f‖₁`. -/
lemma czOp_bounded {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (K : ℝ → ℂ) (Bk : ℝ) (hBk0 : 0 ≤ Bk) (hBk : ∀ z : ℝ, ‖K z‖ ≤ Bk)
    (f : ℝ → H) (hf : Integrable f) :
    ∀ x : ℝ, ‖czOp K f x‖ ≤ Bk * ∫ y, ‖f y‖ := by
  intro x
  have h1 : ‖czOp K f x‖ₑ ≤ ENNReal.ofReal (Bk * ∫ y, ‖f y‖) := by
    calc ‖czOp K f x‖ₑ ≤ ∫⁻ y, ‖K (x - y) • f y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, ENNReal.ofReal Bk * ‖f y‖ₑ := by
          refine lintegral_mono (fun y => ?_)
          rw [enorm_smul, enorm_eq_ofReal_norm', enorm_eq_ofReal_norm']
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hBk _)) _
      _ = ENNReal.ofReal Bk * ∫⁻ y, ‖f y‖ₑ :=
          lintegral_const_mul'' _ hf.aestronglyMeasurable.enorm
      _ = ENNReal.ofReal Bk * ENNReal.ofReal (∫ y, ‖f y‖) := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hf]
      _ = ENNReal.ofReal (Bk * ∫ y, ‖f y‖) := by
          rw [ENNReal.ofReal_mul hBk0]
  rwa [enorm_eq_ofReal_norm', ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1

/-- The strong `(p,p)` bound for `1 < p < 2` for a multiplier satisfying the uniform
Calderón--Zygmund hypotheses.  The constant is linear in `K1`. -/
theorem cz_lp_small_general {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (m : ℝ → ℂ) (B Bk Aker K1 : ℝ) (hB : 0 < B) (hK1 : 1 ≤ K1)
    (hAker : 0 < Aker) (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ B) (hm : Integrable m)
    (hKm : Measurable (czKern m)) (hKbdd : ∀ z : ℝ, ‖czKern m z‖ ≤ Bk)
    (hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      (∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖czKern m (x - y) - czKern m x‖ₑ)
        ≤ ENNReal.ofReal (Aker * K1))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∀ f : ℝ → H, Integrable f →
      eLpNorm (czOp (czKern m) f) (ENNReal.ofReal p)
        ≤ ENNReal.ofReal (((12 * (24 * B ^ 2 + 4 * Aker + 100) * 2 ^ (p - 1) / (p - 1)
            + 16 * B ^ 2 / (2 - p)) ^ (1 / p)) * K1) * eLpNorm f (ENNReal.ofReal p) := by
  intro f hf
  letI : MeasurableSpace H := ⊤
  have hstrong : ∀ g : ℝ → H, Integrable g →
      eLpNorm (fun x : ℝ => ∫ y : ℝ, czKern m (x - y) • g y) 2
        ≤ ENNReal.ofReal B * eLpNorm g 2 := by
    intro g hg
    have h := czOp_czKern_L2 m B hB hmb hm g hg
    rwa [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] at h
  have hweak : ∀ g : ℝ → H, Integrable g → ∀ α : ℝ, 0 < α →
      volume {x : ℝ | α < ‖czOp (czKern m) g x‖}
        ≤ ENNReal.ofReal ((24 * B ^ 2 + 4 * (Aker * K1) + 100) / α) * eLpNorm g 1 :=
    fun g hg α hα => cz_weak_type_one_measurable_bounded (czKern m) B (Aker * K1) Bk hB
      (mul_nonneg (le_of_lt hAker) (by linarith)) hKbdd hKm hker
      (fun g' hg' => hstrong g' hg') g hg α hα
  have hadd : ∀ g₁ g₂ : ℝ → H, Integrable g₁ → Integrable g₂ →
      czOp (czKern m) (g₁ + g₂) = czOp (czKern m) g₁ + czOp (czKern m) g₂ := by
    intro g₁ g₂ hg₁ hg₂
    funext x
    have h1 := Commons.Analysis.Convolution.integrable_smul_sub_of_measurable_bounded
      (czKern m) Bk hKbdd hKm g₁ hg₁ x
    have h2 := Commons.Analysis.Convolution.integrable_smul_sub_of_measurable_bounded
      (czKern m) Bk hKbdd hKm g₂ hg₂ x
    rw [show (czOp (czKern m) (g₁ + g₂)) x
        = ∫ y, (czKern m (x - y) • g₁ y + czKern m (x - y) • g₂ y) from by
      simp only [czOp, Pi.add_apply]
      apply integral_congr_ae
      filter_upwards with y
      rw [smul_add]]
    rw [integral_add h1 h2]
    rfl
  have hA0 : 0 < 24 * B ^ 2 + 4 * (Aker * K1) + 100 := by positivity
  have hmarc :=
    Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (T := fun f : ℝ → H => czOp (czKern m) f) hadd hA0 hB
      (fun g α hg hα => hweak g hg α hα) (fun g hg => hstrong g hg) hp1 hp2 f hf
  have hAmax : 0 < 24 * B ^ 2 + 4 * Aker + 100 := by positivity
  have hA0le : 24 * B ^ 2 + 4 * (Aker * K1) + 100 ≤ (24 * B ^ 2 + 4 * Aker + 100) * K1 := by
    nlinarith [hK1, hAker, sq_nonneg B]
  have h4 := Commons.Analysis.Lp.rpow_marcinkiewicz_const_le hp1 hp2 hB hAmax hK1 hA0 hA0le
  refine hmarc.trans ?_
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h4) _

/-- The adjoint pairing identity for the kernel of the conjugate symbol. -/
lemma czOp_czKern_adjoint_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (m : ℝ → ℂ) (Bk : ℝ) (hKbdd : ∀ z : ℝ, ‖czKern m z‖ ≤ Bk)
    (hKm : Measurable (czKern m)) (hm : Integrable m) (F : SchwartzMap ℝ H) (g : ℝ → H)
    (hg : Integrable g) :
    (∫ x : ℝ, inner ℂ (czOp (czKern m) (F : ℝ → H) x) (g x))
      = ∫ x : ℝ, inner ℂ ((F : ℝ → H) x)
          (czOp (czKernConj m) g x) := by
  have h := Commons.Analysis.Convolution.integral_inner_convolution_eq_adjoint_meas
    (czKern m) Bk hKbdd hKm (F : ℝ → H) g F.integrable hg
  simp only [czOp] at h ⊢
  rw [h]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [show czKernConj m (x - y) = (starRingEnd ℂ) (czKern m (y - x)) from by
    rw [czKernConj, czKern_conj m hm]
    dsimp only
    rw [show -(x - y) = y - x by ring]]

set_option maxHeartbeats 600000 in
/-- The `p > 2` strong bound by duality, given the `p' = p/(p-1) < 2` bound for the adjoint
multiplier. -/
theorem cz_lp_large {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (m m' : ℝ → ℂ) (C Bk : ℝ) (hBk0 : 0 ≤ Bk) (hKbdd : ∀ z : ℝ, ‖czKern m z‖ ≤ Bk)
    (hKm : Measurable (czKern m)) (hKm' : Measurable m') (hm : Integrable m)
    (hpair : ∀ (F : SchwartzMap ℝ H) (g : ℝ → H), Integrable g →
      (∫ x : ℝ, inner ℂ (czOp (czKern m) (F : ℝ → H) x) (g x))
        = ∫ x : ℝ, inner ℂ ((F : ℝ → H) x) (czOp m' g x))
    {p : ℝ} (hp : 2 < p)
    (hdual : ∀ g : ℝ → H, Integrable g →
      eLpNorm (czOp m' g) (ENNReal.ofReal (p / (p - 1)))
        ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (p / (p - 1)))) :
    ∀ F : SchwartzMap ℝ H,
      eLpNorm (czOp (czKern m) (F : ℝ → H)) (ENNReal.ofReal p)
        ≤ ENNReal.ofReal C * eLpNorm (F : ℝ → H) (ENNReal.ofReal p) := by
  intro F
  have hp1 : 1 < p := by linarith
  have hp'1 : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < p - 1)]
    linarith
  have hpq : 1 / p + 1 / (p / (p - 1)) = 1 := by
    field_simp
    ring
  have hsm : AEStronglyMeasurable (czOp (czKern m) (F : ℝ → H)) volume :=
    aestronglyMeasurable_czConv hKm.aestronglyMeasurable F.continuous.aestronglyMeasurable
  have hbdd : ∃ B : ℝ, ∀ x : ℝ, ‖czOp (czKern m) (F : ℝ → H) x‖ ≤ B :=
    ⟨Bk * ∫ y, ‖(F : ℝ → H) y‖,
      fun x => czOp_bounded (czKern m) Bk hBk0 hKbdd (F : ℝ → H) F.integrable x⟩
  have hFlt : eLpNorm (F : ℝ → H) (ENNReal.ofReal p) < ⊤ :=
    (F.memLp (ENNReal.ofReal p) (volume : Measure ℝ)).eLpNorm_lt_top
  apply Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
  · exact hp1
  · exact hsm
  · exact hbdd
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hFlt)
  · intro g hg
    rw [hpair F g hg]
    have hB1 : ‖(∫ x : ℝ, inner ℂ ((F : ℝ → H) x) (czOp m' g x))‖ₑ
        ≤ eLpNorm (F : ℝ → H) (ENNReal.ofReal p)
            * eLpNorm (czOp m' g) (ENNReal.ofReal (p / (p - 1))) := by
      apply Commons.Analysis.Lp.eLpNorm_pairing_le
      · exact hp1
      · exact hp'1
      · exact hpq
      · exact F.continuous.aestronglyMeasurable
      · exact aestronglyMeasurable_czConv hKm'.aestronglyMeasurable hg.aestronglyMeasurable
    have hB2 : eLpNorm (F : ℝ → H) (ENNReal.ofReal p)
          * eLpNorm (czOp m' g) (ENNReal.ofReal (p / (p - 1)))
        ≤ eLpNorm (F : ℝ → H) (ENNReal.ofReal p)
          * (ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (p / (p - 1)))) := by
      apply mul_le_mul_right
      exact hdual g hg
    have hB3 : eLpNorm (F : ℝ → H) (ENNReal.ofReal p)
          * (ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (p / (p - 1))))
        = (ENNReal.ofReal C * eLpNorm (F : ℝ → H) (ENNReal.ofReal p))
          * eLpNorm g (ENNReal.ofReal (p / (p - 1))) := by
      rw [mul_left_comm, mul_assoc]
    exact hB1.trans (hB2.trans hB3.le)

theorem cz_shift {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ) (hC : 0 < C) (Λ : ℝ) (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (p : ℝ) (hp : 1 < p) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (K : ℝ) (hK : 1 ≤ K) (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N)
        (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
        (lam : ℝ → ℝ) (hlam : ∀ N ∈ D, |lam N| ≤ 2 ^ K)
        (ψ : SchwartzMap ℝ ℂ) (hψ0 : ψ 0 = 0)
        (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0)
        (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C)
        (eps : ℝ → ℂ) (heps : ∀ N ∈ D, ‖eps N‖ ≤ 1)
        (F : SchwartzMap ℝ H),
      MeasureTheory.eLpNorm
        (fun x : ℝ => ∫ ξ : ℝ,
          ((∑ N ∈ D, eps N * (ψ (A * N ^ d * ξ)
              * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))))
            * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (F : ℝ → H) ξ))
        (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal (C' * K)
          * MeasureTheory.eLpNorm (fun x : ℝ => F x) (ENNReal.ofReal p) MeasureTheory.volume := by
  obtain ⟨B, hB, hBsym⟩ := czSymb_bound_uniform C Λ A hC hΛ d hd hA
  obtain ⟨Ck, hCk, hCksum⟩ := cz_kernel_sum_le_lintegral C Λ A hC hΛ d hd hA
  rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
  · -- ## case `1 < p < 2`
    refine ⟨(12 * (24 * B ^ 2 + 4 * Ck + 100) * 2 ^ (p - 1) / (p - 1)
        + 16 * B ^ 2 / (2 - p)) ^ (1 / p), ?_, ?_⟩
    · have h2 : (0:ℝ) < 12 * (24 * B ^ 2 + 4 * Ck + 100) * 2 ^ (p - 1) / (p - 1) :=
        div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num) _)) (by linarith)
      have h3 : (0:ℝ) < 16 * B ^ 2 / (2 - p) := div_pos (by positivity) (by linarith)
      exact Real.rpow_pos_of_pos (by linarith) _
    · intro K hK D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps F
      have hm : Integrable (czSymb A d D lam eps (ψ : ℝ → ℂ)) :=
        czSymb_integrable A hA d D hDpos lam eps ψ
      obtain ⟨C₁, hC₁, hdec1, _⟩ :=
        Commons.Analysis.Schwartz.fourierInv_schwartz_decay C hC ψ hψsupp hψj
      have hPhi : ∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ * (1 + t ^ 2)⁻¹ := by
        intro t
        rw [czPhi_eq_fourierInv]
        simpa [div_eq_mul_inv] using hdec1 t
      have hKmeas : Measurable (czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))) :=
        czKern_czSymb_measurable A hA d D hDpos lam eps ψ
      have hKbdd : ∀ z : ℝ, ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) z‖
          ≤ ∑ N ∈ D, C₁ * (A * N ^ d)⁻¹ :=
        czKern_czSymb_bounded A hA d D hDpos lam eps heps ψ C₁ hC₁ hPhi
      have hmb : ∀ ξ : ℝ, ‖czSymb A d D lam eps (ψ : ℝ → ℂ) ξ‖ ≤ B :=
        fun ξ => hBsym D hDpos hlac ψ hψ0 hψsupp hψj lam eps heps ξ
      have hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
          (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) (x - y)
              - czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) x‖ₑ) ≤ ENNReal.ofReal (Ck * K) :=
        fun L hL y hy => czKern_diff_lintegral_le A hA d D hDpos lam eps ψ L y (Ck * K)
          (hCksum K hK D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps L hL y hy)
      have hconv : (fun x : ℝ => ∫ ξ : ℝ,
            ((∑ N ∈ D, eps N * (ψ (A * N ^ d * ξ)
                * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))))
              * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
              • (FourierTransform.fourier (F : ℝ → H) ξ))
          = czOp (czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))) (F : ℝ → H) := by
        rw [czOp_czKern_eq_mult (czSymb A d D lam eps (ψ : ℝ → ℂ)) hm (F : ℝ → H) F.integrable]
        funext x
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [czSymb, czE]
      rw [hconv]
      exact cz_lp_small_general (czSymb A d D lam eps (ψ : ℝ → ℂ)) B
        (∑ N ∈ D, C₁ * (A * N ^ d)⁻¹) Ck K hB hK hCk hmb hm hKmeas hKbdd hker hp hp2
        (F : ℝ → H) F.integrable
  · -- ## case `p = 2`
    refine ⟨B, hB, ?_⟩
    intro K hK D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps F
    have hm : Integrable (czSymb A d D lam eps (ψ : ℝ → ℂ)) :=
      czSymb_integrable A hA d D hDpos lam eps ψ
    have hmb : ∀ ξ : ℝ, ‖czSymb A d D lam eps (ψ : ℝ → ℂ) ξ‖ ≤ B :=
      fun ξ => hBsym D hDpos hlac ψ hψ0 hψsupp hψj lam eps heps ξ
    have hconv : (fun x : ℝ => ∫ ξ : ℝ,
          ((∑ N ∈ D, eps N * (ψ (A * N ^ d * ξ)
              * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))))
            * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (F : ℝ → H) ξ))
        = czOp (czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))) (F : ℝ → H) := by
      rw [czOp_czKern_eq_mult (czSymb A d D lam eps (ψ : ℝ → ℂ)) hm (F : ℝ → H) F.integrable]
      funext x
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [czSymb, czE]
    rw [hp2, hconv]
    refine (czOp_czKern_L2 (czSymb A d D lam eps (ψ : ℝ → ℂ)) B hB hmb hm
      (F : ℝ → H) F.integrable).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact le_mul_of_one_le_right (le_of_lt hB) hK
  · -- ## case `2 < p`
    refine ⟨(12 * (24 * B ^ 2 + 4 * Ck + 100) * 2 ^ (p / (p - 1) - 1) / (p / (p - 1) - 1)
        + 16 * B ^ 2 / (2 - p / (p - 1))) ^ (1 / (p / (p - 1))), ?_, ?_⟩
    · have hp1' : (0:ℝ) < p / (p - 1) - 1 := by
        have he : p / (p - 1) - 1 = 1 / (p - 1) := by
          have hpne : p - 1 ≠ 0 := by linarith
          field_simp
          ring
        rw [he]
        exact div_pos one_pos (by linarith)
      have hp2' : (0:ℝ) < 2 - p / (p - 1) := by
        have he : 2 - p / (p - 1) = (p - 2) / (p - 1) := by
          have hpne : p - 1 ≠ 0 := by linarith
          field_simp
          ring
        rw [he]
        exact div_pos (by linarith) (by linarith)
      have h2 : (0:ℝ) < 12 * (24 * B ^ 2 + 4 * Ck + 100) * 2 ^ (p / (p - 1) - 1)
          / (p / (p - 1) - 1) :=
        div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num) _)) hp1'
      have h3 : (0:ℝ) < 16 * B ^ 2 / (2 - p / (p - 1)) := div_pos (by positivity) hp2'
      exact Real.rpow_pos_of_pos (by linarith) _
    · intro K hK D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps F
      have hp1 : 1 < p := by linarith
      have hp'1 : 1 < p / (p - 1) := by
        rw [lt_div_iff₀ (by linarith : (0:ℝ) < p - 1)]
        linarith
      have hp'2 : p / (p - 1) < 2 := by
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < p - 1)]
        linarith
      have hm : Integrable (czSymb A d D lam eps (ψ : ℝ → ℂ)) :=
        czSymb_integrable A hA d D hDpos lam eps ψ
      obtain ⟨C₁, hC₁, hdec1, _⟩ :=
        Commons.Analysis.Schwartz.fourierInv_schwartz_decay C hC ψ hψsupp hψj
      have hPhi : ∀ t : ℝ, ‖czPhi (ψ : ℝ → ℂ) t‖ ≤ C₁ * (1 + t ^ 2)⁻¹ := by
        intro t
        rw [czPhi_eq_fourierInv]
        simpa [div_eq_mul_inv] using hdec1 t
      have hKmeas : Measurable (czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))) :=
        czKern_czSymb_measurable A hA d D hDpos lam eps ψ
      have hKbdd : ∀ z : ℝ, ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) z‖
          ≤ ∑ N ∈ D, C₁ * (A * N ^ d)⁻¹ :=
        czKern_czSymb_bounded A hA d D hDpos lam eps heps ψ C₁ hC₁ hPhi
      have hmb : ∀ ξ : ℝ, ‖czSymb A d D lam eps (ψ : ℝ → ℂ) ξ‖ ≤ B :=
        fun ξ => hBsym D hDpos hlac ψ hψ0 hψsupp hψj lam eps heps ξ
      have hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
          (∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ‖czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) (x - y)
              - czKern (czSymb A d D lam eps (ψ : ℝ → ℂ)) x‖ₑ) ≤ ENNReal.ofReal (Ck * K) :=
        fun L hL y hy => czKern_diff_lintegral_le A hA d D hDpos lam eps ψ L y (Ck * K)
          (hCksum K hK D hDpos hlac lam hlam ψ hψ0 hψsupp hψj eps heps L hL y hy)
      have hconv : (fun x : ℝ => ∫ ξ : ℝ,
            ((∑ N ∈ D, eps N * (ψ (A * N ^ d * ξ)
                * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))))
              * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
              • (FourierTransform.fourier (F : ℝ → H) ξ))
          = czOp (czKern (czSymb A d D lam eps (ψ : ℝ → ℂ))) (F : ℝ → H) := by
        rw [czOp_czKern_eq_mult (czSymb A d D lam eps (ψ : ℝ → ℂ)) hm (F : ℝ → H) F.integrable]
        funext x
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [czSymb, czE]
      have hdual : ∀ g : ℝ → H, Integrable g →
          eLpNorm (czOp (czKernConj (czSymb A d D lam eps (ψ : ℝ → ℂ))) g)
              (ENNReal.ofReal (p / (p - 1)))
            ≤ ENNReal.ofReal (((12 * (24 * B ^ 2 + 4 * Ck + 100) * 2 ^ (p / (p - 1) - 1)
                / (p / (p - 1) - 1) + 16 * B ^ 2 / (2 - p / (p - 1)))
                ^ (1 / (p / (p - 1)))) * K)
              * eLpNorm g (ENNReal.ofReal (p / (p - 1))) := by
        have hmb' : ∀ ξ : ℝ,
            ‖(starRingEnd ℂ) (czSymb A d D lam eps (ψ : ℝ → ℂ) ξ)‖ ≤ B := by
          intro ξ
          rw [Complex.norm_conj]
          exact hmb ξ
        have hm' : Integrable (fun ξ : ℝ =>
            (starRingEnd ℂ) (czSymb A d D lam eps (ψ : ℝ → ℂ) ξ)) :=
          integrable_star_comp _ hm
        have hKm' : Measurable (czKern (fun ξ : ℝ =>
            (starRingEnd ℂ) (czSymb A d D lam eps (ψ : ℝ → ℂ) ξ))) := by
          rw [czKern_conj _ hm]
          exact continuous_star.measurable.comp (hKmeas.comp continuous_neg.measurable)
        have hKbdd' : ∀ z : ℝ, ‖czKern (fun ξ : ℝ =>
            (starRingEnd ℂ) (czSymb A d D lam eps (ψ : ℝ → ℂ) ξ)) z‖
            ≤ ∑ N ∈ D, C₁ * (A * N ^ d)⁻¹ := by
          intro z
          rw [czKern_conj _ hm]
          dsimp only
          rw [Complex.norm_conj]
          exact hKbdd (-z)
        have hker' := czKern_conj_hker (czSymb A d D lam eps (ψ : ℝ → ℂ)) hm (Ck * K) hker
        exact cz_lp_small_general
          (fun ξ : ℝ => (starRingEnd ℂ) (czSymb A d D lam eps (ψ : ℝ → ℂ) ξ))
          B (∑ N ∈ D, C₁ * (A * N ^ d)⁻¹) Ck K hB hK hCk hmb' hm' hKm' hKbdd' hker'
          hp'1 hp'2
      rw [hconv]
      refine cz_lp_large (czSymb A d D lam eps (ψ : ℝ → ℂ))
        (czKernConj (czSymb A d D lam eps (ψ : ℝ → ℂ)))
        (((12 * (24 * B ^ 2 + 4 * Ck + 100) * 2 ^ (p / (p - 1) - 1) / (p / (p - 1) - 1)
            + 16 * B ^ 2 / (2 - p / (p - 1))) ^ (1 / (p / (p - 1)))) * K)
        (∑ N ∈ D, C₁ * (A * N ^ d)⁻¹)
        (Finset.sum_nonneg (fun N hN => mul_nonneg (le_of_lt hC₁)
          (le_of_lt (inv_pos.mpr (mul_pos hA (pow_pos (hDpos N hN) d))))))
        hKbdd hKmeas ?_ hm ?_ hp2 ?_ F
      · rw [czKernConj, czKern_conj _ hm]
        exact continuous_star.measurable.comp (hKmeas.comp continuous_neg.measurable)
      · intro F' g hg
        exact czOp_czKern_adjoint_pairing (czSymb A d D lam eps (ψ : ℝ → ℂ))
          (∑ N ∈ D, C₁ * (A * N ^ d)⁻¹) hKbdd hKmeas hm F' g hg
      · exact hdual

end

end Commons.Analysis.CalderonZygmund
