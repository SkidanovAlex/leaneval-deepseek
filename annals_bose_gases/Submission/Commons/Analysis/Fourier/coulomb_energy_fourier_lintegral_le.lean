import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.RCLike.Inner
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Commons.Analysis.Fourier.per_s_energy_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 800000

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace FourierTransform
open Complex hiding exp

namespace Commons.Analysis.Fourier

/-! ## Basic helper lemmas -/

lemma heatR_nonneg' {s : ℝ} (hs : 0 ≤ s) (z : V3) : 0 ≤ heatR s z := heatK_nonneg hs z

lemma heatR_le' {s : ℝ} (hs : 0 ≤ s) (z : V3) : heatR s z ≤ s ^ (-(3 / 2 : ℝ)) := heatK_le_rpow hs z

lemma gaussR_integrable (s : ℝ) (hs : 0 < s) : Integrable (fun p : V3 => gaussR s p) := by
  have hb : 0 < Real.pi * s := by positivity
  have hbC : 0 < (((Real.pi * s : ℝ)) : ℂ).re := by simpa using hb
  have hG : Integrable (fun v : V3 => Complex.exp (-(((Real.pi * s : ℝ)) : ℂ) * (‖v‖ : ℂ) ^ 2)) := by
    simpa using (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V3)
      (b := (((Real.pi * s : ℝ)) : ℂ)) hbC (0 : ℂ) (0 : V3))
  have hnorm : ∀ v : V3,
      ‖Complex.exp (-(((Real.pi * s : ℝ)) : ℂ) * (‖v‖ : ℂ) ^ 2)‖ = gaussR s v := by
    intro v
    rw [Complex.norm_exp]
    simp only [gaussR]
    congr 1
    have harg : -(((Real.pi * s : ℝ)) : ℂ) * (‖v‖ : ℂ) ^ 2 = ((-(Real.pi * s * ‖v‖ ^ 2) : ℝ) : ℂ) := by
      norm_cast
      ring
    rw [harg, Complex.ofReal_re]
  refine Integrable.congr hG.norm ?_
  filter_upwards [] with v
  exact hnorm v

lemma gaussR_continuous (s : ℝ) : Continuous (fun p : V3 => gaussR s p) := by
  unfold gaussR; fun_prop

lemma gaussR_nonneg (s : ℝ) (p : V3) : 0 ≤ gaussR s p := (Real.exp_pos _).le

lemma lintegral_ofReal_heatR_eq (z : V3) (hz : z ≠ 0) :
    (∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (heatR s z)) = ENNReal.ofReal (‖z‖⁻¹) := by
  have hind : Integrable (fun s : ℝ => heatK s z) (volume.restrict (Set.Ioi (0:ℝ))) :=
    heatK_integrable_Ioi hz
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun s : ℝ => heatK s z) :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun s hs => heatK_nonneg (le_of_lt hs) z)
  have hconv : (fun s : ℝ => ENNReal.ofReal (heatR s z)) = fun s => ENNReal.ofReal (heatK s z) := by
    funext s; rfl
  rw [hconv, ← ofReal_integral_eq_lintegral_ofReal hind hnn, heatK_Ioi hz]

lemma ofReal_inv_norm_sq_eq_pi_lintegral_gauss (p : V3) (hp : p ≠ 0) :
    ENNReal.ofReal (1/‖p‖^2)
      = ENNReal.ofReal Real.pi * ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (gaussR s p) := by
  have hpnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hb : 0 < Real.pi * ‖p‖^2 := by positivity
  have hneg : -(Real.pi * ‖p‖^2) < 0 := by linarith
  have hind0 : IntegrableOn (fun s : ℝ => Real.exp ((-(Real.pi * ‖p‖^2)) * s)) (Set.Ioi (0:ℝ)) :=
    integrableOn_exp_mul_Ioi hneg 0
  have hae : (fun s : ℝ => Real.exp ((-(Real.pi * ‖p‖^2)) * s)) = fun s => gaussR s p := by
    funext s
    simp only [gaussR]
    congr 1
    ring
  have hind : Integrable (fun s : ℝ => gaussR s p) (volume.restrict (Set.Ioi (0:ℝ))) := by
    rw [← hae]; exact hind0
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun s : ℝ => gaussR s p) :=
    Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)
  have hint : (∫ s : ℝ in Set.Ioi (0:ℝ), gaussR s p) = 1/(Real.pi * ‖p‖^2) := by
    have hkey := integral_exp_neg_mul_rpow (p := 1) (b := Real.pi * ‖p‖^2) zero_lt_one hb
    simp only [Real.rpow_one, div_one, mul_one] at hkey
    rw [show (1:ℝ) + 1 = 2 by norm_num, Real.Gamma_two, mul_one, Real.rpow_neg_one] at hkey
    rw [← hae, hkey, one_div]
  rw [← ofReal_integral_eq_lintegral_ofReal hind hnn, hint]
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.pi)]
  congr 1
  field_simp

lemma inner_heatR_integrable (f : V3 → ℝ) (hf : Integrable f) {s : ℝ} (hs : 0 < s) (x : V3) :
    Integrable (fun y : V3 => f y * heatR s (x - y)) := by
  refine Integrable.mono' (hf.norm.mul_const (s ^ (-(3/2:ℝ)))) ?_ ?_
  · have hcont : Continuous (fun y : V3 => heatR s (x - y)) :=
      (heatK_continuous hs).comp (continuous_const.sub continuous_id)
    exact hf.1.mul hcont.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatR_nonneg' hs.le (x-y)), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (heatR_le' hs.le (x-y)) (abs_nonneg _)

lemma inner_heatR_abs_le (f : V3 → ℝ) (hf : Integrable f) {s : ℝ} (hs : 0 < s) (x : V3) :
    |∫ y : V3, f y * heatR s (x - y)| ≤ (∫ y : V3, ‖f y‖) * s ^ (-(3/2:ℝ)) := by
  calc |∫ y : V3, f y * heatR s (x - y)|
      ≤ ∫ y : V3, ‖f y * heatR s (x - y)‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y : V3 => f y * heatR s (x-y))
    _ ≤ ∫ y : V3, ‖f y‖ * s ^ (-(3/2:ℝ)) :=
        integral_mono (inner_heatR_integrable f hf hs x).norm (hf.norm.mul_const _) (fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatR_nonneg' hs.le (x-y)), Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (heatR_le' hs.le (x-y)) (abs_nonneg _))
    _ = (∫ y : V3, ‖f y‖) * s ^ (-(3/2:ℝ)) := by rw [integral_mul_const]

lemma outer_heatR_integrable (f : V3 → ℝ) (hf : Integrable f) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : V3 => f x * (∫ y : V3, f y * heatR s (x - y))) := by
  have hmeas : AEStronglyMeasurable (fun x : V3 => ∫ y : V3, f y * heatR s (x - y)) volume :=
    AEStronglyMeasurable.integral_prod_right' (α := V3) (β := V3) (E := ℝ)
      (f := fun z : V3 × V3 => f z.2 * heatR s (z.1 - z.2)) (by
        have hcont : Continuous (fun z : V3 × V3 => heatR s (z.1 - z.2)) :=
          (heatK_continuous hs).comp (continuous_fst.sub continuous_snd)
        exact (hf.1.comp_snd).mul hcont.aestronglyMeasurable)
  refine Integrable.mono' (hf.norm.mul_const ((∫ y : V3, ‖f y‖) * s ^ (-(3/2:ℝ)))) ?_ ?_
  · exact hf.1.mul hmeas
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (inner_heatR_abs_le f hf hs x) (abs_nonneg _)

lemma ofReal_inner_heatR (f : V3 → ℝ) (hf : Integrable f) (hf0 : 0 ≤ f) {s : ℝ} (hs : 0 < s) (x : V3) :
    ENNReal.ofReal (∫ y : V3, f y * heatR s (x - y))
      = ∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (heatR s (x - y)) := by
  have hnn : 0 ≤ᵐ[volume] (fun y : V3 => f y * heatR s (x - y)) :=
    Filter.Eventually.of_forall (fun y => mul_nonneg (hf0 y) (heatR_nonneg' hs.le _))
  rw [ofReal_integral_eq_lintegral_ofReal (inner_heatR_integrable f hf hs x) hnn]
  apply lintegral_congr_ae
  filter_upwards with y
  rw [ENNReal.ofReal_mul (hf0 y)]

lemma ofReal_outer_heatR (f : V3 → ℝ) (hf : Integrable f) (hf0 : 0 ≤ f) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (∫ x : V3, f x * (∫ y : V3, f y * heatR s (x - y)))
      = ∫⁻ x, ENNReal.ofReal (f x) * (∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (heatR s (x - y))) := by
  have hnn : 0 ≤ᵐ[volume] (fun x : V3 => f x * (∫ y : V3, f y * heatR s (x - y))) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (hf0 x)
      (integral_nonneg (fun y => mul_nonneg (hf0 y) (heatR_nonneg' hs.le _))))
  rw [ofReal_integral_eq_lintegral_ofReal (outer_heatR_integrable f hf hs) hnn]
  apply lintegral_congr_ae
  filter_upwards with x
  rw [ENNReal.ofReal_mul (hf0 x), ofReal_inner_heatR f hf hf0 hs x]

/-! ## The `R` integrand and measurability -/

def coulR (f : V3 → ℝ) (s : ℝ) (q : V3 × V3) : ENNReal :=
  ENNReal.ofReal (f q.1) * ENNReal.ofReal (f q.2) * ENNReal.ofReal (heatR s (q.1 - q.2))

lemma measurable_heatR_joint : Measurable (fun z : ℝ × (V3 × V3) => heatR z.1 (z.2.1 - z.2.2)) := by
  unfold heatR; measurability

lemma aemeasurable_coulR_section (f : V3 → ℝ) (hf : AEStronglyMeasurable f volume)
    {s : ℝ} (hs : 0 < s) :
    AEMeasurable (fun q : V3 × V3 => coulR f s q) (volume.prod volume) := by
  unfold coulR
  exact AEMeasurable.mul
    (AEMeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable (hf.aemeasurable.comp_fst))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hf.aemeasurable.comp_snd)))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((heatK_measurable hs).comp (measurable_fst.sub measurable_snd)).aemeasurable)

lemma aemeasurable_coulR_joint (f : V3 → ℝ) (hf : AEStronglyMeasurable f volume) :
    AEMeasurable (fun z : ℝ × (V3 × V3) => coulR f z.1 z.2)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.prod volume)) := by
  unfold coulR
  exact AEMeasurable.mul
    (AEMeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable (hf.aemeasurable.comp_fst.comp_snd))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hf.aemeasurable.comp_snd.comp_snd)))
    (ENNReal.measurable_ofReal.comp_aemeasurable (measurable_heatR_joint.aemeasurable))

/-! ## Main assembly -/

theorem coulomb_energy_fourier_lintegral_eq {f : V3 → ℝ} (hf : Integrable f) (hf0 : 0 ≤ f) :
    (∫⁻ p, ENNReal.ofReal (‖FourierTransform.fourier (fun x => (f x : ℂ)) p‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal Real.pi * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) := by
  set F : V3 → ℂ := fun x => (f x : ℂ) with hFdef
  have hFint : Integrable F := hf.ofReal
  have hCfint : Integrable (fun y : V3 => ‖F y‖) := hFint.norm
  set Cf : ℝ := ∫ y : V3, ‖F y‖ with hCfdef
  have hCf0 : 0 ≤ Cf := by rw [hCfdef]; exact integral_nonneg (fun y => norm_nonneg _)
  have hFnorm_le : ∀ p : V3, ‖𝓕 F p‖ ≤ Cf := by
    intro p; rw [hCfdef]; exact ft_norm_le F p hFint
  have ha_le : ∀ p : V3, ‖𝓕 F p‖ ^ 2 ≤ Cf ^ 2 := fun p =>
    pow_le_pow_left₀ (norm_nonneg _) (hFnorm_le p) 2
  have hFmeas : AEStronglyMeasurable (fun p : V3 => 𝓕 F p) volume := by
    have heq : (fun p : V3 => 𝓕 F p)
        = fun p => ∫ x : V3, Complex.exp ((↑(-2 * Real.pi * ⟪x, p⟫) : ℂ) * Complex.I) • F x := by
      funext p; rw [Real.fourier_eq']
    rw [heq]
    refine AEStronglyMeasurable.integral_prod_right' (α := V3) (β := V3) (E := ℂ)
      (f := fun z : V3 × V3 =>
        Complex.exp ((↑(-2 * Real.pi * ⟪z.2, z.1⟫) : ℂ) * Complex.I) • F z.2) ?_
    have hcont : Continuous (fun z : V3 × V3 =>
        Complex.exp ((↑(-2 * Real.pi * ⟪z.2, z.1⟫) : ℂ) * Complex.I)) := by
      fun_prop
    exact hcont.aestronglyMeasurable.smul (hFint.1.comp_snd)
  -- integrability of the momentum slice
  have hInt_a : ∀ s : ℝ, 0 < s → Integrable (fun p : V3 => ‖𝓕 F p‖ ^ 2 * gaussR s p) := by
    intro s hs
    refine Integrable.mono' ((gaussR_integrable s hs).const_mul (Cf ^ 2)) ?_ ?_
    · exact ((hFmeas.norm.pow 2).mul ((gaussR_continuous s).aestronglyMeasurable))
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gaussR_nonneg s p))]
      exact mul_le_mul_of_nonneg_right (ha_le p) (gaussR_nonneg s p)
  -- Step 1: pointwise Laplace expansion a.e. in p
  have hpne : ∀ᵐ p : V3, p ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    rw [show {p : V3 | ¬ p ≠ 0} = {0} by ext p; simp]
    exact measure_singleton 0
  have hpt : ∀ᵐ p : V3, ENNReal.ofReal (‖𝓕 F p‖ ^ 2 / ‖p‖ ^ 2)
      = ENNReal.ofReal Real.pi *
          ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p) := by
    filter_upwards [hpne] with p hp
    calc ENNReal.ofReal (‖𝓕 F p‖ ^ 2 / ‖p‖ ^ 2)
        = ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (1 / ‖p‖ ^ 2) := by
            rw [div_eq_mul_one_div, ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (‖𝓕 F p‖ ^ 2) *
            (ENNReal.ofReal Real.pi * ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (gaussR s p)) := by
            rw [ofReal_inv_norm_sq_eq_pi_lintegral_gauss p hp]
      _ = ENNReal.ofReal Real.pi * (ENNReal.ofReal (‖𝓕 F p‖ ^ 2) *
            ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (gaussR s p)) := by
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (‖𝓕 F p‖ ^ 2)) (ENNReal.ofReal Real.pi), mul_assoc]
      _ = ENNReal.ofReal Real.pi *
            ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hA1 : AEMeasurable (Function.uncurry (fun p (s : ℝ) =>
        ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p)))
      (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    unfold Function.uncurry
    have hmm : AEMeasurable (fun p : V3 => ENNReal.ofReal (‖𝓕 F p‖ ^ 2)) volume :=
      (ENNReal.measurable_ofReal.comp
        ((continuous_norm.pow 2).measurable : Measurable (fun z : ℂ => ‖z‖ ^ 2))).comp_aemeasurable
        hFmeas.aemeasurable
    have hg : Measurable (fun z : V3 × ℝ => gaussR z.2 z.1) := by unfold gaussR; measurability
    exact AEMeasurable.mul hmm.comp_fst
      (ENNReal.measurable_ofReal.comp_aemeasurable hg.aemeasurable)
  have hstep12 : (∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal Real.pi *
          ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p) := by
    calc (∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2 / ‖p‖ ^ 2))
        = ∫⁻ p, ENNReal.ofReal Real.pi *
            ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p) :=
              lintegral_congr_ae hpt
      _ = ENNReal.ofReal Real.pi *
            ∫⁻ p, ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal Real.pi *
            ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p) := by
              congr 1
              rw [MeasureTheory.lintegral_lintegral_swap hA1]
  -- Step 3: convert the p-lintegral to ofReal of the real integral
  have hstep3 : (∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p))
      = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (∫ p : V3, ‖𝓕 F p‖ ^ 2 * gaussR s p) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 < s := hs
    have hnn : 0 ≤ᵐ[volume] (fun p : V3 => ‖𝓕 F p‖ ^ 2 * gaussR s p) :=
      Filter.Eventually.of_forall (fun p => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
    rw [show (fun p : V3 => ENNReal.ofReal (‖𝓕 F p‖ ^ 2) * ENNReal.ofReal (gaussR s p))
          = fun p => ENNReal.ofReal (‖𝓕 F p‖ ^ 2 * gaussR s p) by
          funext p; rw [ENNReal.ofReal_mul (sq_nonneg _)]]
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt_a s hs') hnn]
  -- Step 4: per-s identity (delegated lemma)
  have hper : ∀ s ∈ Set.Ioi (0:ℝ),
      (∫ p : V3, ‖𝓕 F p‖ ^ 2 * gaussR s p)
        = ∫ x : V3, f x * (∫ y : V3, f y * heatR s (x - y)) := by
    intro s hs
    exact per_s_energy_integrable hf hs
  have hstep34 : (∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (∫ p : V3, ‖𝓕 F p‖ ^ 2 * gaussR s p))
      = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (∫ x : V3, f x * (∫ y : V3, f y * heatR s (x - y))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [hper s hs]
  have hL1 : (∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal Real.pi *
          ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (∫ x : V3, f x * (∫ y : V3, f y * heatR s (x - y))) := by
    rw [hstep12, hstep3, hstep34]
  -- Step 5: expand ofReal of the position double integral
  have hstep5 : (∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (∫ x : V3, f x * (∫ y : V3, f y * heatR s (x - y))))
      = ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ x, ∫⁻ y, coulR f s (x, y) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 < s := hs
    rw [ofReal_outer_heatR f hf hf0 hs']
    apply lintegral_congr_ae
    filter_upwards with x
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards with y
    simp only [coulR, mul_assoc]
  -- Step 6: Tonelli swap s with (x,y)
  have hstep6 : (∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ x, ∫⁻ y, coulR f s (x, y))
      = ∫⁻ x, ∫⁻ y, ∫⁻ s in Set.Ioi (0:ℝ), coulR f s (x, y) := by
    have hJ : AEMeasurable (fun z : ℝ × (V3 × V3) => coulR f z.1 z.2)
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.prod volume)) :=
      aemeasurable_coulR_joint f hf.1
    have hpart : AEMeasurable (fun q : V3 × V3 => ∫⁻ s in Set.Ioi (0:ℝ), coulR f s q)
        (volume.prod volume) := AEMeasurable.lintegral_prod_left hJ
    calc (∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ x, ∫⁻ y, coulR f s (x, y))
        = ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ q : V3 × V3, coulR f s q ∂(volume.prod volume) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
            rw [MeasureTheory.lintegral_lintegral (f := fun x y => coulR f s (x, y))
              (aemeasurable_coulR_section f hf.1 hs)]
      _ = ∫⁻ z : ℝ × (V3 × V3), coulR f z.1 z.2
            ∂((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.prod volume)) := by
            rw [MeasureTheory.lintegral_lintegral (f := fun s q => coulR f s q) hJ]
      _ = ∫⁻ q : V3 × V3, (∫⁻ s in Set.Ioi (0:ℝ), coulR f s q) ∂(volume.prod volume) := by
            rw [MeasureTheory.lintegral_prod_symm (f := fun z : ℝ × (V3 × V3) => coulR f z.1 z.2) hJ]
      _ = ∫⁻ x, ∫⁻ y, ∫⁻ s in Set.Ioi (0:ℝ), coulR f s (x, y) := by
            rw [← MeasureTheory.lintegral_lintegral
              (f := fun x y => ∫⁻ s in Set.Ioi (0:ℝ), coulR f s (x, y)) hpart]
  -- Step 7: collapse the s-integral using the heat kernel
  have hstep7 : (∫⁻ x, ∫⁻ y, ∫⁻ s in Set.Ioi (0:ℝ), coulR f s (x, y))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) := by
    apply lintegral_congr_ae
    filter_upwards with x
    apply lintegral_congr_ae
    filter_upwards [show ∀ᵐ y : V3, y ≠ x from by
      rw [MeasureTheory.ae_iff]
      rw [show {y : V3 | ¬ y ≠ x} = {x} by ext y; simp]
      exact measure_singleton x] with y hy
    have hyx : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    simp only [coulR]
    rw [lintegral_const_mul _ (by unfold heatR; measurability)]
    rw [lintegral_ofReal_heatR_eq (x - y) hyx]
    rw [← ENNReal.ofReal_mul (hf0 x)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hf0 x) (hf0 y))]
    rw [div_eq_mul_inv]
  calc (∫⁻ p, ENNReal.ofReal (‖𝓕 F p‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal Real.pi *
          ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (∫ x : V3, f x * (∫ y : V3, f y * heatR s (x - y))) := hL1
    _ = ENNReal.ofReal Real.pi * ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ x, ∫⁻ y, coulR f s (x, y) := by rw [hstep5]
    _ = ENNReal.ofReal Real.pi * ∫⁻ x, ∫⁻ y, ∫⁻ s in Set.Ioi (0:ℝ), coulR f s (x, y) := by rw [hstep6]
    _ = ENNReal.ofReal Real.pi * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) := by rw [hstep7]

/-- The main statement: the momentum-space Coulomb energy is at most `π` times
the position-space Coulomb energy, stated as an inequality of Lebesgue integrals. -/
theorem coulomb_energy_fourier_lintegral_le {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.Integrable f) (hf0 : 0 ≤ f) :
    ∫⁻ p, ENNReal.ofReal (‖FourierTransform.fourier (fun x => (f x : ℂ)) p‖ ^ 2 / ‖p‖ ^ 2) ≤
      ENNReal.ofReal Real.pi * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) :=
  le_of_eq (coulomb_energy_fourier_lintegral_eq hf hf0)

end Commons.Analysis.Fourier
