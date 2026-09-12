import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

namespace Commons.Analysis.Potential

open MeasureTheory
open scoped NNReal

noncomputable section

/-- The `ℝ≥0∞`-valued Gaussian kernel `exp(-a‖z-w‖²)` on `ℂ × ℂ`. -/
private def gaussK (a : ℝ) : ℂ × ℂ → ENNReal :=
  fun p => ENNReal.ofReal (Real.exp (-a * ‖p.1 - p.2‖ ^ 2))

private lemma measurable_gaussK (a : ℝ) : Measurable (gaussK a) := by
  unfold gaussK
  fun_prop

private lemma measurable_gaussK_left (a : ℝ) (t : ℂ) :
    Measurable (fun z : ℂ => gaussK a (z, t)) :=
  (measurable_gaussK a).comp (measurable_id.prodMk measurable_const)

private lemma measurable_gaussK_right (a : ℝ) (z : ℂ) :
    Measurable (fun t : ℂ => gaussK a (z, t)) :=
  (measurable_gaussK a).comp (measurable_const.prodMk measurable_id)

private lemma measurable_gaussK_pair (a : ℝ) :
    Measurable (fun q : ℂ × (ℂ × ℂ) => gaussK a (q.2.1, q.1) * gaussK a (q.2.2, q.1)) := by
  have h1 : Measurable (fun q : ℂ × (ℂ × ℂ) => gaussK a (q.2.1, q.1)) :=
    (measurable_gaussK a).comp (Measurable.prodMk (measurable_fst.comp measurable_snd) measurable_fst)
  have h2 : Measurable (fun q : ℂ × (ℂ × ℂ) => gaussK a (q.2.2, q.1)) :=
    (measurable_gaussK a).comp (Measurable.prodMk (measurable_snd.comp measurable_snd) measurable_fst)
  exact h1.mul h2

/-- The `t ↦ ∫ z, exp(-a‖z-t‖²) dμ z` Gaussian transform of a measure. -/
private def gaussH (a : ℝ) (μ : Measure ℂ) : ℂ → ENNReal :=
  fun t => ∫⁻ z, gaussK a (z, t) ∂μ

private lemma measurable_gaussH (a : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable (gaussH a μ) := by
  unfold gaussH
  refine Measurable.lintegral_prod_left (μ := μ) (f := fun z t => gaussK a (z, t)) ?_
  have hfun : Function.uncurry (fun z t => gaussK a (z, t)) = gaussK a := by
    funext p; simp [Function.uncurry, gaussK]
  rw [hfun]; exact measurable_gaussK a

/-- Gaussian total mass on `ℂ` (which is `ℝ²`). -/
private lemma gauss_volume_C (b : ℝ) (hb : 0 < b) :
    (∫ t : ℂ, Real.exp (-b * ‖t‖ ^ 2)) = Real.pi / b := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := b) hb
  rw [Complex.finrank_real_complex] at h
  simpa using h

/-- Translation invariance plus total mass of the `ℝ≥0∞`-valued Gaussian on `ℂ`. -/
private lemma lin_gauss_translate (b : ℝ) (hb : 0 < b) (m : ℂ) :
    (∫⁻ t : ℂ, gaussK b (t, m)) = ENNReal.ofReal (Real.pi / b) := by
  have hInt : Integrable (fun t : ℂ => Real.exp (-b * ‖t‖ ^ 2)) volume :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm b hb
  have hIntm : Integrable (fun t : ℂ => Real.exp (-b * ‖t - m‖ ^ 2)) volume :=
    hInt.comp_sub_right m
  unfold gaussK
  rw [← ofReal_integral_eq_lintegral_ofReal hIntm (ae_of_all _ (fun t => (Real.exp_pos _).le))]
  rw [integral_sub_right_eq_self (fun t : ℂ => Real.exp (-b * ‖t‖ ^ 2)) m]
  rw [gauss_volume_C b hb]

/-- The pointwise "completion of the square" identity for two Gaussian factors. -/
private lemma exp_sq_split (u : ℝ) (z w t : ℂ) :
    Real.exp (-(2 * u) * ‖z - t‖ ^ 2) * Real.exp (-(2 * u) * ‖w - t‖ ^ 2) =
      Real.exp (-(4 * u) * ‖t - (z + w) / 2‖ ^ 2) * Real.exp (-u * ‖z - w‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_re, Complex.div_im]
  norm_num
  ring

/-- The pointwise identity for the `ℝ≥0∞`-valued Gaussian kernels. -/
private lemma gaussK_split (u : ℝ) (z w t : ℂ) :
    gaussK (2 * u) (z, t) * gaussK (2 * u) (w, t) =
      gaussK (4 * u) (t, (z + w) / 2) * gaussK u (z, w) := by
  have h1 : 0 ≤ Real.exp (-(2 * u) * ‖z - t‖ ^ 2) := (Real.exp_pos _).le
  have h3 : 0 ≤ Real.exp (-(4 * u) * ‖t - (z + w) / 2‖ ^ 2) := (Real.exp_pos _).le
  unfold gaussK
  rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h3]
  congr 1
  simpa using exp_sq_split u z w t

/-- Key Gaussian convolution computation: the `L²` pairing of two shifted Gaussians. -/
private lemma inner_kernel (u : ℝ) (hu : 0 < u) (z w : ℂ) :
    (∫⁻ t : ℂ, gaussK (2 * u) (z, t) * gaussK (2 * u) (w, t)) =
      ENNReal.ofReal (Real.pi / (4 * u)) * gaussK u (z, w) := by
  calc (∫⁻ t : ℂ, gaussK (2 * u) (z, t) * gaussK (2 * u) (w, t))
      = ∫⁻ t : ℂ, gaussK (4 * u) (t, (z + w) / 2) * gaussK u (z, w) :=
        lintegral_congr (fun t => gaussK_split u z w t)
    _ = (∫⁻ t : ℂ, gaussK (4 * u) (t, (z + w) / 2)) * gaussK u (z, w) :=
        lintegral_mul_const _ (measurable_gaussK_left (4 * u) ((z + w) / 2))
    _ = ENNReal.ofReal (Real.pi / (4 * u)) * gaussK u (z, w) := by
        rw [lin_gauss_translate (4 * u) (by linarith) ((z + w) / 2)]

/-- Binary AM–GM in `ℝ≥0`. -/
private lemma amgm_nnreal (a b : ℝ≥0) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  have := two_mul_le_add_sq a b
  simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using this

/-- Binary AM–GM in `ℝ≥0∞`. -/
private lemma amgm_ennreal (a b : ENNReal) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with ha | ha
  · subst ha
    rcases eq_or_ne b 0 with hb | hb
    · subst hb; simp
    · rw [ENNReal.top_mul hb, ENNReal.mul_top (by norm_num : (2 : ENNReal) ≠ 0)]
      simp
  rcases eq_or_ne b ⊤ with hb | hb
  · subst hb
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0; simp
    · rw [ENNReal.mul_top ha0]
      simp
  have ha' : a = ((a.toNNReal : ℝ≥0) : ENNReal) := (ENNReal.coe_toNNReal ha).symm
  have hb' : b = ((b.toNNReal : ℝ≥0) : ENNReal) := (ENNReal.coe_toNNReal hb).symm
  rw [ha', hb']
  have h2 : (2 : ENNReal) = ↑(2 : ℝ≥0) := (ENNReal.coe_ofNat 2).symm
  rw [h2, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
      ← ENNReal.coe_add]
  exact ENNReal.coe_le_coe.mpr (by
    have := two_mul_le_add_sq a.toNNReal b.toNNReal
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using this)

/-- The cross term: integrating `H_μ · H_ν` against Lebesgue measure recovers the
`(μ × ν)`-energy of the Gaussian kernel, up to the total Gaussian mass. -/
private lemma cross_integral (u : ℝ) (hu : 0 < u) (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) ν t ∂volume) =
      ENNReal.ofReal (Real.pi / (4 * u)) *
        (∫⁻ p : ℂ × ℂ, gaussK u p ∂(μ.prod ν)) := by
  have hstep : ∀ t, gaussH (2 * u) μ t * gaussH (2 * u) ν t
      = ∫⁻ p : ℂ × ℂ, gaussK (2 * u) (p.1, t) * gaussK (2 * u) (p.2, t) ∂(μ.prod ν) := by
    intro t
    simp only [gaussH]
    exact (lintegral_prod_mul (f := fun z => gaussK (2 * u) (z, t))
      (g := fun w => gaussK (2 * u) (w, t))
      (measurable_gaussK_left _ _).aemeasurable (measurable_gaussK_left _ _).aemeasurable).symm
  calc (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) ν t ∂volume)
      = ∫⁻ t, (∫⁻ p : ℂ × ℂ,
          gaussK (2 * u) (p.1, t) * gaussK (2 * u) (p.2, t) ∂(μ.prod ν)) ∂volume :=
        lintegral_congr hstep
    _ = ∫⁻ p : ℂ × ℂ,
          (∫⁻ t, gaussK (2 * u) (p.1, t) * gaussK (2 * u) (p.2, t) ∂volume) ∂(μ.prod ν) := by
        rw [lintegral_lintegral_swap (μ := volume) (ν := μ.prod ν)
          (f := fun t p => gaussK (2 * u) (p.1, t) * gaussK (2 * u) (p.2, t))
          (measurable_gaussK_pair (2 * u)).aemeasurable]
    _ = ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (Real.pi / (4 * u)) * gaussK u p ∂(μ.prod ν) := by
        apply lintegral_congr; intro p
        rw [inner_kernel u hu p.1 p.2]
    _ = ENNReal.ofReal (Real.pi / (4 * u)) * (∫⁻ p : ℂ × ℂ, gaussK u p ∂(μ.prod ν)) :=
        lintegral_const_mul _ (measurable_gaussK u)

theorem gauss_kernel_cs (μ ν : MeasureTheory.Measure ℂ) [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] {u : ℝ} (hu : 0 < u) :
    2 * MeasureTheory.lintegral (μ.prod ν) (fun z : ℂ × ℂ => ENNReal.ofReal (Real.exp (-u * ‖z.1 - z.2‖ ^ 2)))
      ≤ MeasureTheory.lintegral (μ.prod μ) (fun z : ℂ × ℂ => ENNReal.ofReal (Real.exp (-u * ‖z.1 - z.2‖ ^ 2)))
        + MeasureTheory.lintegral (ν.prod ν) (fun z : ℂ × ℂ => ENNReal.ofReal (Real.exp (-u * ‖z.1 - z.2‖ ^ 2))) := by
  haveI : SFinite μ := inferInstance
  haveI : SFinite ν := inferInstance
  change 2 * (∫⁻ p : ℂ × ℂ, gaussK u p ∂(μ.prod ν))
      ≤ (∫⁻ p : ℂ × ℂ, gaussK u p ∂(μ.prod μ))
        + (∫⁻ p : ℂ × ℂ, gaussK u p ∂(ν.prod ν))
  set R : ENNReal := ENNReal.ofReal (Real.pi / (4 * u)) with hR
  set A : ENNReal := ∫⁻ p : ℂ × ℂ, gaussK u p ∂(μ.prod ν) with hA
  set B : ENNReal := ∫⁻ p : ℂ × ℂ, gaussK u p ∂(μ.prod μ) with hB
  set D : ENNReal := ∫⁻ p : ℂ × ℂ, gaussK u p ∂(ν.prod ν) with hD
  have h1 : (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) ν t ∂volume) = R * A := by
    rw [hR, hA]; exact cross_integral u hu μ ν
  have h2 : (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) μ t ∂volume) = R * B := by
    rw [hR, hB]; exact cross_integral u hu μ μ
  have h3 : (∫⁻ t, gaussH (2 * u) ν t * gaussH (2 * u) ν t ∂volume) = R * D := by
    rw [hR, hD]; exact cross_integral u hu ν ν
  have hmeasν : Measurable (gaussH (2 * u) ν) := measurable_gaussH _ _
  have hmeasμ : Measurable (gaussH (2 * u) μ) := measurable_gaussH _ _
  have hamgm : 2 * (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) ν t ∂volume)
      ≤ (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) μ t ∂volume)
        + (∫⁻ t, gaussH (2 * u) ν t * gaussH (2 * u) ν t ∂volume) := by
    have hpt : ∀ t, 2 * (gaussH (2 * u) μ t * gaussH (2 * u) ν t)
        ≤ gaussH (2 * u) μ t * gaussH (2 * u) μ t
          + gaussH (2 * u) ν t * gaussH (2 * u) ν t :=
      fun t => by
        have h := amgm_ennreal (gaussH (2 * u) μ t) (gaussH (2 * u) ν t)
        simpa only [pow_two] using h
    calc 2 * (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) ν t ∂volume)
        = ∫⁻ t, 2 * (gaussH (2 * u) μ t * gaussH (2 * u) ν t) ∂volume :=
          (lintegral_const_mul (2 : ENNReal) (hmeasμ.mul hmeasν)).symm
      _ ≤ ∫⁻ t, (gaussH (2 * u) μ t * gaussH (2 * u) μ t
            + gaussH (2 * u) ν t * gaussH (2 * u) ν t) ∂volume :=
          lintegral_mono hpt
      _ = (∫⁻ t, gaussH (2 * u) μ t * gaussH (2 * u) μ t ∂volume)
            + (∫⁻ t, gaussH (2 * u) ν t * gaussH (2 * u) ν t ∂volume) :=
          lintegral_add_left (hmeasμ.mul hmeasμ) _
  rw [h1, h2, h3] at hamgm
  have key : R * (2 * A) ≤ R * (B + D) := by
    have he : 2 * (R * A) = R * (2 * A) := by ring
    have hf : R * B + R * D = R * (B + D) := by rw [mul_add]
    rw [he, hf] at hamgm
    exact hamgm
  have hR0 : R ≠ 0 := by rw [hR]; exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hRt : R ≠ ⊤ := by rw [hR]; exact ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hR0 hRt).mp key

end

end Commons.Analysis.Potential