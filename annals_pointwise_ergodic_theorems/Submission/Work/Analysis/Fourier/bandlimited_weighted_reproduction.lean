/-
# The `L¹`-free weighted reproducing bound for band-limited functions

The published `Commons.Analysis.Fourier.bandlimited_reconstruction_real` /
`bandlimited_decaying_kernel_bound` give the weighted domination
`‖f x‖ ≤ A ∫ ‖f y‖ (1+‖x−y‖)^{-N}` for band-limited `f` that is **integrable** (`L¹`).  The sharp
arc cutoff of the corpus's major-arc model produces band-limited functions that are *not* `L¹`
(their samples decay only like `1/m`), so those lemmas do not apply.

This file proves the bound **without** any integrability hypothesis on the band-limited function:
everything is expressed through the *amplitude* `W` of its inverse Fourier transform, and the
reproducing identity `h x = ∫ h y · w (x - y) dy` for the reproducing kernel `w` (`𝓕w ≡ 1` on the
support of `W`) is then a *Fubini* computation on the amplitude side, where absolute integrability
is manifest.
-/

import Mathlib
import Submission.Commons.Analysis.MeasureTheory.lintegral_mul_rpow_le_rpow_mul_lintegral
import Submission.Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le

open MeasureTheory Set Finset
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

noncomputable section

set_option maxHeartbeats 800000

/-- **Weighted reproducing bound, `L¹`-free.**  Let `W` be integrable and let `w` be integrable with
`‖w z‖ ≤ B/(1+z²)` and `𝓕w ≡ 1` on the support of `W`.  Then the inverse Fourier transform of `W` is
dominated by the polynomially weighted integral of itself. -/
theorem norm_fourierInv_le_weighted {W w : ℝ → ℂ} (hW : Integrable W) (hw : Integrable w)
    {B : ℝ} (hB : 0 < B) (hwdec : ∀ z : ℝ, ‖w z‖ ≤ B / (1 + z ^ 2))
    (hprod : ∀ β : ℝ, W β ≠ 0 → FourierTransform.fourier w β = 1) (x : ℝ) :
    ‖FourierTransformInv.fourierInv W x‖
      ≤ B * ∫ y : ℝ, ‖FourierTransformInv.fourierInv W y‖ / (1 + (x - y) ^ 2) := by
  -- (i) the reproducing identity at each frequency: a reflection/translation computation
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
  -- integrability of the Fubini integrand on the product space
  have hprodint : Integrable (Function.uncurry
      (fun y β : ℝ =>
        (Complex.exp (↑(2 * Real.pi * inner ℝ β y) * Complex.I) • W β) * w (x - y)))
      (volume.prod volume) := by
    refine Integrable.mono' (Integrable.mul_prod (hw.norm.comp_sub_left x) hW.norm) ?_ ?_
    · have h1 : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I))
          (volume.prod volume) :=
        (by fun_prop : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I))).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2) (volume.prod volume) :=
        hW.aestronglyMeasurable.comp_snd
      have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => w (x - p.1)) (volume.prod volume) :=
        (hw.comp_sub_left x).aestronglyMeasurable.comp_fst
      have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          Complex.exp (↑(2 * Real.pi * inner ℝ p.2 p.1) * Complex.I) * W p.2
            * w (x - p.1)) (volume.prod volume) := by
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
  -- (ii) the weighted domination
  have hbdd : ∀ y : ℝ, ‖FourierTransformInv.fourierInv W y‖ ≤ ∫ β : ℝ, ‖W β‖ := by
    intro y
    rw [Real.fourierInv_eq']
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with β
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcont : Continuous (FourierTransformInv.fourierInv W) := by
    have h1 : (⇑(Real.Lp.fourierTransformInv
          (MemLp.toLp W (memLp_one_iff_integrable.mpr hW))) : ℝ → ℂ)
        = FourierTransformInv.fourierInv W := Real.Lp.fourierTransformInv_toLp _
    rw [← h1]
    exact (Real.Lp.fourierTransformInv _).continuous
  have hcnt : AEStronglyMeasurable
      (fun y : ℝ => ‖FourierTransformInv.fourierInv W y‖) volume :=
    hcont.norm.aestronglyMeasurable
  have hwint : Integrable (fun y : ℝ => B / (1 + (x - y) ^ 2)) := by
    have h1 : Integrable (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.comp_sub_left x
    simpa only [div_eq_mul_inv] using h1.const_mul B
  calc ‖FourierTransformInv.fourierInv W x‖
      = ‖∫ y : ℝ, FourierTransformInv.fourierInv W y * w (x - y)‖ := by rw [hrep]
    _ ≤ ∫ y : ℝ, ‖FourierTransformInv.fourierInv W y * w (x - y)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ‖FourierTransformInv.fourierInv W y‖ * ‖w (x - y)‖ := by
        simp only [norm_mul]
    _ ≤ ∫ y : ℝ, ‖FourierTransformInv.fourierInv W y‖ * (B / (1 + (x - y) ^ 2)) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => by positivity)
          (Integrable.bdd_mul hwint hcnt (Filter.Eventually.of_forall fun y => by
            simpa using hbdd y))
          (Filter.Eventually.of_forall fun y =>
            mul_le_mul_of_nonneg_left (hwdec (x - y)) (norm_nonneg _))
    _ = B * ∫ y : ℝ, ‖FourierTransformInv.fourierInv W y‖ / (1 + (x - y) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [div_eq_mul_inv]
        ring


/-! ## The weighted lattice sandwich, `L¹`-free

With the reproducing bound of the previous section in hand, the whole ENNReal sandwich of
`Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow` can be rerun with the
**hypothesis `Integrable` on the band-limited function removed**: only the *amplitude* `W` must be
integrable, and the reproducing kernel `w` must satisfy `𝓕w ≡ 1` on the support of `W`.  This is the
form needed for the sharp major-arc cutoffs of the circle method, where the band-limited function
itself has only `1/m`-decay and is not in `L¹`. -/

lemma summable_inv_one_add_sq_sub (t : ℝ) :
    Summable (fun m : ℤ => (1 + ((m : ℝ) - t) ^ 2)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((Commons.Analysis.Fourier.summable_one_add_sq_int).mul_left (2 * (1 + t ^ 2)))
  have hkey : 1 + (m : ℝ) ^ 2 ≤ (2 * (1 + t ^ 2)) * (1 + ((m : ℝ) - t) ^ 2) := by
    nlinarith [sq_nonneg ((m : ℝ) - 2 * t), sq_nonneg t]
  rw [show (2 * (1 + t ^ 2)) * (1 + (m : ℝ) ^ 2)⁻¹
      = ((1 + (m : ℝ) ^ 2) / (2 * (1 + t ^ 2)))⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [hkey]

private lemma tsum_ofReal_inv_one_add_sq_sub_le' :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      (∑' m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - t) ^ 2)⁻¹)) ≤ ENNReal.ofReal B := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
  refine ⟨B, hBpos, fun t => ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (summable_inv_one_add_sq_sub t)]
  exact ENNReal.ofReal_le_ofReal (hB t)

private lemma lintegral_ofReal_inv_one_add_sq_sub_le' (x : ℝ) :
    (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹)) ≤ ENNReal.ofReal Real.pi := by
  have htrans : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (y + (-x)) ^ 2)⁻¹))
      = ∫⁻ y : ℝ, ENNReal.ofReal ((1 + y ^ 2)⁻¹) :=
    lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => ENNReal.ofReal ((1 + y ^ 2)⁻¹)) (-x)
  have hfun : (fun y : ℝ => ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹))
      = fun y : ℝ => ENNReal.ofReal ((1 + (y + (-x)) ^ 2)⁻¹) := by
    funext y
    rw [show (1 + (x - y) ^ 2 : ℝ) = 1 + (y + (-x)) ^ 2 by ring]
  rw [hfun, htrans, ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
    (Filter.Eventually.of_forall (fun y => by positivity)), integral_univ_inv_one_add_sq]

/-- **The `ℓ^p` lattice maximal bound for band-limited families given by an `L¹` amplitude.**
For `p > 1` there is `C > 0` such that for every family of integrable amplitudes `W j` and every
integrable reproducing kernel `w` with `‖w z‖ ≤ B/(1+z²)` and `𝓕w ≡ 1` on `⋃_j supp (W j)`,

`∫⁻_ℤ (⨆_j ‖𝓕⁻(W j)‖)^p ≤ ofReal (C · B^p) · ∫⁻_ℝ (⨆_j ‖𝓕⁻(W j)‖)^p`,

with `C` independent of `W`, `w` and `B`.  This is
`Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow` without the
`Integrable (𝓕⁻(W j))` hypothesis (which fails for the sharp major-arc cutoffs). -/
theorem lattice_sup_le_integral_sup_band_limited_fourierInv_rpow {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ → ℝ → ℂ) (w : ℝ → ℂ) (B : ℝ),
      (∀ j : ℕ, Integrable (W j)) → Integrable w → 0 < B →
      (∀ z : ℝ, ‖w z‖ ≤ B / (1 + z ^ 2)) →
      (∀ (j : ℕ) (β : ℝ), W j β ≠ 0 → FourierTransform.fourier w β = 1) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖FourierTransformInv.fourierInv (W j) (m : ℝ)‖ₑ) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * B ^ p) *
          ∫⁻ x : ℝ, (⨆ j : ℕ, ‖FourierTransformInv.fourierInv (W j) x‖ₑ) ^ p
            ∂MeasureTheory.volume := by
  obtain ⟨B', hB'pos, hB'⟩ := tsum_ofReal_inv_one_add_sq_sub_le'
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hPpos : 0 < Real.pi ^ (p - 1) := Real.rpow_pos_of_pos Real.pi_pos (p - 1)
  refine ⟨Real.pi ^ (p - 1) * B', mul_pos hPpos hB'pos, ?_⟩
  intro W w B hW hw hB hwdec hprod
  set F : ℝ → ENNReal := fun x => ⨆ j : ℕ, ENNReal.ofReal ‖FourierTransformInv.fourierInv (W j) x‖
    with hF
  have hcontj : ∀ j : ℕ, Continuous (FourierTransformInv.fourierInv (W j)) := by
    intro j
    have h1 : (⇑(Real.Lp.fourierTransformInv
          (MemLp.toLp (W j) (memLp_one_iff_integrable.mpr (hW j)))) : ℝ → ℂ)
        = FourierTransformInv.fourierInv (W j) := Real.Lp.fourierTransformInv_toLp _
    rw [← h1]
    exact (Real.Lp.fourierTransformInv _).continuous
  have hFmeas : Measurable F := by
    rw [hF]
    exact Measurable.iSup (fun j => ENNReal.measurable_ofReal.comp ((hcontj j).norm.measurable))
  have hFae : AEMeasurable F (volume : Measure ℝ) := hFmeas.aemeasurable
  have hbound : ∀ x : ℝ, F x ≤ ENNReal.ofReal B *
      ∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
    intro x
    refine iSup_le (fun j => ?_)
    have hbdd : ∀ y : ℝ, ‖FourierTransformInv.fourierInv (W j) y‖
        ≤ ∫ β : ℝ, ‖W j β‖ := by
      intro y
      rw [Real.fourierInv_eq']
      refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
      apply integral_congr_ae
      filter_upwards with β
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hcntj : AEStronglyMeasurable
        (fun y : ℝ => ‖FourierTransformInv.fourierInv (W j) y‖) volume :=
      (hcontj j).norm.aestronglyMeasurable
    have hwi : Integrable (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.comp_sub_left x
    have hφint : Integrable
        (fun y : ℝ => ‖FourierTransformInv.fourierInv (W j) y‖ / (1 + (x - y) ^ 2)) := by
      have h := Integrable.bdd_mul hwi hcntj
        (Filter.Eventually.of_forall (fun y => by simpa using hbdd y))
      simpa only [div_eq_mul_inv] using h
    have hreal := norm_fourierInv_le_weighted (hW j) hw hB hwdec (hprod j) x
    calc ENNReal.ofReal ‖FourierTransformInv.fourierInv (W j) x‖
        ≤ ENNReal.ofReal (B * ∫ y : ℝ,
            ‖FourierTransformInv.fourierInv (W j) y‖ / (1 + (x - y) ^ 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal B * ENNReal.ofReal (∫ y : ℝ,
            ‖FourierTransformInv.fourierInv (W j) y‖ / (1 + (x - y) ^ 2)) :=
          ENNReal.ofReal_mul hB.le
      _ = ENNReal.ofReal B * ∫⁻ y : ℝ, ENNReal.ofReal
            (‖FourierTransformInv.fourierInv (W j) y‖ / (1 + (x - y) ^ 2)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hφint
            (Filter.Eventually.of_forall fun y => by positivity)]
      _ ≤ ENNReal.ofReal B * ∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
          apply mul_le_mul_right
          apply lintegral_mono
          intro y
          change ENNReal.ofReal (‖FourierTransformInv.fourierInv (W j) y‖ / (1 + (x - y) ^ 2))
            ≤ F y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹)
          rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 1 + (x - y) ^ 2),
            ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < 1 + (x - y) ^ 2),
            div_eq_mul_inv]
          rw [hF]
          exact mul_le_mul_left (le_iSup
            (fun j => ENNReal.ofReal ‖FourierTransformInv.fourierInv (W j) y‖) j) _
  have hstep : ∀ m : ℤ, F (m : ℝ) ^ p
      ≤ ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
        ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
    intro m
    have hb := hbound (m : ℝ)
    have hVmeas : Measurable
        (fun y : ℝ => ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) :=
      ENNReal.measurable_ofReal.comp
        (Continuous.measurable (Continuous.inv₀
          (continuous_const.add ((continuous_const.sub continuous_id).pow 2))
          (fun y => by positivity)))
    have hjensen :=
      Commons.Analysis.MeasureTheory.lintegral_mul_rpow_le_rpow_mul_lintegral hp hFae
        hVmeas.aemeasurable
    have hVpi : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))
        ≤ ENNReal.ofReal Real.pi := lintegral_ofReal_inv_one_add_sq_sub_le' _
    calc F (m : ℝ) ^ p
        ≤ (ENNReal.ofReal B *
            ∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p :=
          ENNReal.rpow_le_rpow hb hp0.le
      _ = ENNReal.ofReal (B ^ p) *
            (∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
            ENNReal.ofReal_rpow_of_nonneg hB.le hp0.le]
      _ ≤ ENNReal.ofReal (B ^ p) *
            ((∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ (p - 1) *
              ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) :=
          mul_le_mul_right hjensen _
      _ ≤ ENNReal.ofReal (B ^ p) *
            (ENNReal.ofReal Real.pi ^ (p - 1) *
              ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) := by
          apply mul_le_mul_right
          exact mul_le_mul_left (ENNReal.rpow_le_rpow hVpi hp1) _
      _ = ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_rpow_of_nonneg Real.pi_pos.le hp1, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hB p).le]
  have hVmeasZ : ∀ y : ℝ, Measurable
      (fun m : ℤ => ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) := fun y =>
    measurable_of_countable _
  have hcount : ∀ y : ℝ,
      (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) ∂Measure.count)
        ≤ ENNReal.ofReal B' := by
    intro y
    rw [lintegral_count]
    exact hB' y
  have hpair : Measurable (Function.uncurry (fun (m : ℤ) (y : ℝ) =>
      F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))) := by
    show Measurable (fun q : ℤ × ℝ =>
      F q.2 ^ p * ENNReal.ofReal ((1 + ((q.1 : ℝ) - q.2) ^ 2)⁻¹))
    refine Measurable.mul ?_ ?_
    · exact (hFmeas.comp measurable_snd).pow_const p
    · refine ENNReal.measurable_ofReal.comp ?_
      have h2 : Measurable (fun q : ℤ × ℝ => (1 + ((q.1 : ℝ) - q.2) ^ 2 : ℝ)) := by fun_prop
      exact measurable_inv.comp h2
  have hmain : (∫⁻ m : ℤ, F (m : ℝ) ^ p ∂Measure.count)
      ≤ ENNReal.ofReal ((Real.pi ^ (p - 1) * B') * B ^ p) * ∫⁻ x : ℝ, F x ^ p ∂volume := by
    calc (∫⁻ m : ℤ, F (m : ℝ) ^ p ∂Measure.count)
        ≤ ∫⁻ m : ℤ, ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
            (∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))
              ∂Measure.count := lintegral_mono hstep
      _ = ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ m : ℤ, (∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))
              ∂Measure.count := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, (∫⁻ m : ℤ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)
              ∂Measure.count) ∂volume := by
          congr 1
          rw [lintegral_lintegral_swap]
          exact hpair.aemeasurable
      _ = ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, F y ^ p *
              (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) ∂Measure.count)
              ∂volume := by
          congr 1
          apply lintegral_congr
          intro y
          rw [lintegral_const_mul (F y ^ p) (hVmeasZ y)]
      _ ≤ ENNReal.ofReal (B ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal B' ∂volume := by
          apply mul_le_mul_right
          apply lintegral_mono
          intro y
          change F y ^ p * (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)
              ∂Measure.count) ≤ F y ^ p * ENNReal.ofReal B'
          exact mul_le_mul_right (hcount y) _
      _ = ENNReal.ofReal ((Real.pi ^ (p - 1) * B') * B ^ p) *
            ∫⁻ y : ℝ, F y ^ p ∂volume := by
          rw [lintegral_mul_const _ (hFmeas.pow_const p),
            mul_comm (∫⁻ y : ℝ, F y ^ p ∂volume) (ENNReal.ofReal B'), ← mul_assoc,
            ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_pos_of_pos hB p).le hPpos.le)]
          congr 1
          ring
  have hL : (∫⁻ m : ℤ, (⨆ j : ℕ, ‖FourierTransformInv.fourierInv (W j) (m : ℝ)‖ₑ) ^ p
      ∂Measure.count) = ∫⁻ m : ℤ, F (m : ℝ) ^ p ∂Measure.count := by
    apply lintegral_congr
    intro m
    rw [hF]
    simp only [← ofReal_norm]
  have hR : (∫⁻ x : ℝ, (⨆ j : ℕ, ‖FourierTransformInv.fourierInv (W j) x‖ₑ) ^ p ∂volume)
      = ∫⁻ x : ℝ, F x ^ p ∂volume := by
    apply lintegral_congr
    intro x
    rw [hF]
    simp only [← ofReal_norm]
  rw [hL, hR]
  exact hmain

end

end Commons.Analysis.Fourier
