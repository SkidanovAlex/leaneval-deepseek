import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.OneBodyKin.BoxHat.boxHat_scale
import Submission.Work.OneBodyKin.CrossKern
import Submission.Work.OneBodyKin.fourier_convScale_scaling
import Submission.Work.OneBodyKin.kinFT_chi_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The indicator of the unit box and its Fourier transform -/

/-- The indicator of the unit centred cube `acube 1`, as a real function. -/
noncomputable def boxInd : ℝ³ → ℝ := (acube 1).indicator (fun _ => (1 : ℝ))

lemma boxInd_of_mem {s : ℝ³} (hs : s ∈ acube 1) : boxInd s = 1 :=
  Set.indicator_of_mem hs _

lemma boxInd_of_notMem {s : ℝ³} (hs : s ∉ acube 1) : boxInd s = 0 :=
  Set.indicator_of_notMem hs _

lemma neg_mem_acube_one {s : ℝ³} : -s ∈ acube 1 ↔ s ∈ acube 1 := by
  simp only [mem_acube_iff, Set.mem_Icc]
  constructor
  · intro h m
    have h' := h m
    replace h' : -(s.ofLp m) ∈ Set.Icc (-1/2) (1/2) := by simpa using h'
    exact ⟨by linarith [h'.2], by linarith [h'.1]⟩
  · intro h m
    have h' := h m
    have hcoe : (-s).ofLp m = -(s.ofLp m) := by simp
    rw [hcoe]
    exact ⟨by linarith [h'.2], by linarith [h'.1]⟩

lemma boxInd_even (s : ℝ³) : boxInd (-s) = boxInd s := by
  by_cases hs : s ∈ acube 1
  · rw [boxInd_of_mem ((neg_mem_acube_one).2 hs), boxInd_of_mem hs]
  · rw [boxInd_of_notMem (fun h => hs ((neg_mem_acube_one).1 h)), boxInd_of_notMem hs]

lemma abs_boxInd_le_one (s : ℝ³) : |boxInd s| ≤ 1 := by
  by_cases hs : s ∈ acube 1
  · rw [boxInd_of_mem hs]; norm_num
  · rw [boxInd_of_notMem hs]; norm_num

lemma integrable_boxInd : Integrable boxInd volume := by
  haveI : IsFiniteMeasure (volume.restrict (acube 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, acube_volume 1 (by norm_num)]
        exact ENNReal.ofReal_lt_top⟩
  have h := (MeasureTheory.integrable_indicator_iff (acube_measurable 1) (μ := volume)
    (f := fun _ : ℝ³ => (1 : ℝ))).mpr (integrable_const (1 : ℝ))
  rwa [boxInd]

/-- The unit centred cube is contained in the Euclidean unit ball. -/
lemma norm_le_one_of_mem_acube {s : ℝ³} (hs : s ∈ acube 1) : ‖s‖ ≤ 1 := by
  have hcoord : ∀ m : Fin 3, |s.ofLp m| ≤ 1 / 2 := fun m => by
    have h := (mem_acube_iff 1 s).mp hs m
    rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hsq : ‖s‖ ^ 2 ≤ (3 / 4 : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ m : Fin 3, ‖s.ofLp m‖ ^ 2 ≤ ∑ _m : Fin 3, ((1 / 2 : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro m _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord m) 2
      _ = 3 * ((1 / 2 : ℝ) ^ 2) := by simp
      _ ≤ 3 / 4 := by norm_num
  nlinarith [norm_nonneg s]

/-- **Geometric support bound.**  If `s` lies in the unit box and `χ(s + ℓ⁻¹ d) ≠ 0`, then
`‖d‖ ≤ 3ℓ/2`: indeed `‖s + ℓ⁻¹d‖ ≤ 1/2` (the support of `χ`), `‖s‖ ≤ 1`, so
`ℓ⁻¹‖d‖ ≤ 3/2`. -/
lemma chi_shift_eq_zero_of_gt {ℓ : ℝ} (hℓ : 0 < ℓ) {s d : ℝ³} (hs : s ∈ acube 1)
    (h : 3 * ℓ / 2 < ‖d‖) : chi (s + ℓ⁻¹ • d) = 0 := by
  by_contra hc
  have h1 : ‖s + ℓ⁻¹ • d‖ ≤ 1 / 2 := by
    by_contra h2
    exact hc (chi_eq_zero_of_norm_gt _ (by linarith))
  have hinv : ‖ℓ⁻¹ • d‖ = ℓ⁻¹ * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  have h2 : ℓ⁻¹ * ‖d‖ ≤ 1 / 2 + 1 := by
    rw [← hinv]
    calc ‖ℓ⁻¹ • d‖ = ‖(s + ℓ⁻¹ • d) - s‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖s + ℓ⁻¹ • d‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ 1 / 2 + 1 := add_le_add h1 (norm_le_one_of_mem_acube hs)
  have h3 : ℓ⁻¹ * (3 * ℓ / 2) = 3 / 2 := by
    field_simp
  have h4 : ℓ⁻¹ * ‖d‖ > 3 / 2 := by
    rw [← h3]
    exact mul_lt_mul_of_pos_left h (inv_pos.mpr hℓ)
  linarith

/-- The sup-norm bound on `χ` used for the domination estimates. -/
lemma abs_chi_le : ∀ x : ℝ³, |chi x| ≤ (Real.sqrt chiNormSq)⁻¹ := by
  intro x
  rw [abs_of_nonneg (chi_nonneg x)]
  exact chi_le_sqrt_inv x

/-! ## 2. The Fourier profile is bounded by the mass of the bump -/

theorem profHat_abs_le (p : ℝ³) :
    |profHat p| ≤ ∫ z : ℝ³, |chi z| := by
  have hchi_int : Integrable (fun z : ℝ³ => |chi z|) volume :=
    (chi_continuous.abs.integrable_of_hasCompactSupport (μ := volume) chi_hasCompactSupport.abs)
  have hc : Continuous (fun z : ℝ³ => chi z * Real.cos (inner ℝ p z)) :=
    chi_continuous.mul (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  have hprod_int : Integrable (fun z : ℝ³ => chi z * Real.cos (inner ℝ p z)) volume :=
    hc.integrable_of_hasCompactSupport (μ := volume) chi_hasCompactSupport.mul_right
  have hbound : |profHat p| ≤ ∫ z : ℝ³, |chi z * Real.cos (inner ℝ p z)| := by
    rw [profHat]
    exact abs_integral_le_integral_abs
  refine hbound.trans ?_
  apply integral_mono_of_nonneg (ae_of_all _ (fun z => abs_nonneg _)) hchi_int
  filter_upwards with z
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)



/-! ## 3. The Fourier transform of the box indicator and the box profile -/

theorem kinFT_boxInd (c : ℝ³) :
    Submission.BoseGases.kinFT (fun z : ℝ³ => (boxInd z : ℂ)) c = (boxHat 1 c : ℂ) := by
  have hcont : Continuous (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ c y : ℂ)))) := by
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
  have hnorm : ∀ y : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ c y : ℂ)))‖ = 1 := by
    intro y
    have h : -(Complex.I * (inner ℝ c y : ℂ)) = ((-(inner ℝ c y) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  haveI : IsFiniteMeasure (volume.restrict (acube 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, acube_volume 1 (by norm_num)]
        exact ENNReal.ofReal_lt_top⟩
  have hf : Integrable (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ))
      volume := by
    have hpt2 : (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ))
        = (acube 1).indicator (fun y => Complex.exp (-(Complex.I * (inner ℝ c y : ℂ)))) := by
      funext y
      by_cases hy : y ∈ acube 1
      · rw [Set.indicator_of_mem hy, boxInd_of_mem hy]; simp
      · rw [Set.indicator_of_notMem hy, boxInd_of_notMem hy]; simp
    rw [hpt2, MeasureTheory.integrable_indicator_iff (acube_measurable 1)]
    refine MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable 1 ?_
    filter_upwards with y
    rw [hnorm y]
  have hexp : ∀ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ c y : ℂ)))
      = ((Real.cos (inner ℝ c y) : ℝ) : ℂ) - ((Real.sin (inner ℝ c y) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [show -(Complex.I * (inner ℝ c y : ℂ)) = ((-(inner ℝ c y) : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hpt : ∀ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)
      = ((boxInd y * Real.cos (inner ℝ c y) : ℝ) : ℂ)
        + ((-(boxInd y * Real.sin (inner ℝ c y)) : ℝ) : ℂ) * Complex.I := by
    intro y; rw [hexp y]; push_cast; ring
  have hre_pt : ∀ y : ℝ³,
      (Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).re
        = boxInd y * Real.cos (inner ℝ c y) := by
    intro y; rw [hpt y]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have him_pt : ∀ y : ℝ³,
      (Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).im
        = -(boxInd y * Real.sin (inner ℝ c y)) := by
    intro y; rw [hpt y]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have hsinzero : (∫ y : ℝ³, boxInd y * Real.sin (inner ℝ c y)) = 0 := by
    have hinv := Submission.BoseGases.integral_comp_neg
      (fun y : ℝ³ => boxInd y * Real.sin (inner ℝ c y))
    have hshift : (∫ y : ℝ³, (fun y : ℝ³ => boxInd y * Real.sin (inner ℝ c y)) (-y))
        = -(∫ y : ℝ³, boxInd y * Real.sin (inner ℝ c y)) := by
      rw [← MeasureTheory.integral_neg]
      apply integral_congr_ae
      filter_upwards with y
      rw [boxInd_even]
      simp only [inner_neg_right, Real.sin_neg]
      ring
    rw [hshift] at hinv
    linarith
  rw [Submission.BoseGases.kinFT]
  apply Complex.ext
  · have hre : (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).re
        = ∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).re := by
      have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
      simpa using this.symm
    rw [hre]
    rw [show (∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).re)
          = ∫ y : ℝ³, boxInd y * Real.cos (inner ℝ c y) from by
      apply integral_congr_ae
      filter_upwards with y
      exact hre_pt y]
    rw [show (∫ y : ℝ³, boxInd y * Real.cos (inner ℝ c y))
          = ∫ y in acube 1, Real.cos (inner ℝ c y) from by
      rw [show (fun y : ℝ³ => boxInd y * Real.cos (inner ℝ c y))
            = (acube 1).indicator (fun y => Real.cos (inner ℝ c y)) from by
        funext y
        by_cases hy : y ∈ acube 1
        · rw [boxInd_of_mem hy, Set.indicator_of_mem hy, one_mul]
        · rw [boxInd_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]]
      rw [MeasureTheory.integral_indicator (acube_measurable 1)]]
    simp [boxHat]
  · have him : (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).im
        = ∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).im := by
      have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hf
      simpa using this.symm
    rw [him]
    rw [show (∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ c y : ℂ))) * (boxInd y : ℂ)).im)
          = ∫ y : ℝ³, -(boxInd y * Real.sin (inner ℝ c y)) from by
      apply integral_congr_ae
      filter_upwards with y
      exact him_pt y]
    rw [MeasureTheory.integral_neg, hsinzero, neg_zero]
    simp [boxHat]

/-- **The exponential integral over the unit box is the box Fourier profile.** -/
theorem integral_exp_box (c : ℝ³) :
    (∫ s in acube 1, Complex.exp (Complex.I * (inner ℝ c s : ℂ))) = (boxHat 1 c : ℂ) := by
  have h1 : (∫ s in acube 1, Complex.exp (Complex.I * (inner ℝ c s : ℂ)))
      = Submission.BoseGases.kinFT (fun z : ℝ³ => (boxInd z : ℂ)) (-c) := by
    rw [Submission.BoseGases.kinFT]
    rw [show (∫ s in acube 1, Complex.exp (Complex.I * (inner ℝ c s : ℂ)))
          = ∫ z, (acube 1).indicator (fun z => Complex.exp (Complex.I * (inner ℝ c z : ℂ))) z from by
      rw [MeasureTheory.integral_indicator (acube_measurable 1)]]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ acube 1
    · simp only [Set.indicator_of_mem hz, boxInd_of_mem hz, Complex.ofReal_one, one_mul]
      congr 1
      rw [inner_neg_left]
      push_cast
      ring
    · simp only [Set.indicator_of_notMem hz, boxInd_of_notMem hz, Complex.ofReal_zero, zero_mul,
        mul_zero]
  rw [h1, kinFT_boxInd (-c), boxHat_even]

/-! ## 3b. The translation Fourier identity -/

private lemma ft_hexp (t : ℝ) :
    Complex.exp (-(Complex.I * (t : ℂ))) = ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [show -(Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast; ring

lemma integral_chi_mul_exp (c : ℝ³) :
    (∫ x : ℝ³, (chi x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ c x : ℂ)))) = (profHat c : ℂ) := by
  rw [← kinFT_chi_eq c, Submission.BoseGases.kinFT]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_comm]

lemma integrable_chi_mul_exp (c : ℝ³) :
    Integrable (fun x : ℝ³ => (chi x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ c x : ℂ)))) volume := by
  have hcont : Continuous (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ c x : ℂ)))) := by
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
  exact ((Complex.continuous_ofReal.comp chi_continuous).mul hcont).integrable_of_hasCompactSupport
    (μ := volume) ((chi_hasCompactSupport.comp_left (by simp)).mul_right)

/-- Pointwise reduction of the translation Fourier identity to real trigonometry. -/
private lemma cos_translate_ft_pointwise (ξ b : ℝ³) (x : ℝ³) :
    Complex.exp (-(Complex.I * (inner ℝ ξ x : ℂ))) * ((chi x * Real.cos (inner ℝ b x) : ℝ) : ℂ)
      = (1 / 2 : ℂ) * ((chi x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (ξ - b) x : ℂ)))
          + (chi x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (ξ + b) x : ℂ)))) := by
  set t1 : ℝ := inner ℝ ξ x
  set t2 : ℝ := inner ℝ b x
  have hsub : inner ℝ (ξ - b) x = t1 - t2 := by simp [t1, t2, inner_sub_left]
  have hadd : inner ℝ (ξ + b) x = t1 + t2 := by simp [t1, t2, inner_add_left]
  rw [hsub, hadd, ft_hexp t1, ft_hexp (t1 - t2), ft_hexp (t1 + t2)]
  push_cast
  rw [Complex.cos_sub, Complex.cos_add, Complex.sin_sub, Complex.sin_add]
  ring

theorem cos_translate_ft (ξ b σ : ℝ³) :
    (∫ w : ℝ³,
        Complex.exp (-(Complex.I * (inner ℝ ξ w : ℂ))) *
          ((chi (σ + w) * Real.cos (inner ℝ b (σ + w)) : ℝ) : ℂ))
      = Complex.exp (Complex.I * (inner ℝ ξ σ : ℂ)) *
          (((1 / 2 : ℝ) * (profHat (ξ - b) + profHat (ξ + b)) : ℝ) : ℂ) := by
  have hphase : ∀ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ ξ (x - σ) : ℂ)))
      = Complex.exp (Complex.I * (inner ℝ ξ σ : ℂ)) *
        Complex.exp (-(Complex.I * (inner ℝ ξ x : ℂ))) := by
    intro x
    rw [show -(Complex.I * (inner ℝ ξ (x - σ) : ℂ))
          = Complex.I * (inner ℝ ξ σ : ℂ) + (-(Complex.I * (inner ℝ ξ x : ℂ))) from by
      rw [inner_sub_right]; push_cast; ring]
    rw [Complex.exp_add]
  have hcompute : (∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ ξ x : ℂ))) *
        ((chi x * Real.cos (inner ℝ b x) : ℝ) : ℂ))
      = (((1 / 2 : ℝ) * (profHat (ξ - b) + profHat (ξ + b)) : ℝ) : ℂ) := by
    rw [show (∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ ξ x : ℂ))) *
          ((chi x * Real.cos (inner ℝ b x) : ℝ) : ℂ))
        = ∫ x : ℝ³, (1 / 2 : ℂ) * ((chi x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (ξ - b) x : ℂ)))
            + (chi x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (ξ + b) x : ℂ)))) from by
      apply integral_congr_ae
      filter_upwards with x
      exact cos_translate_ft_pointwise ξ b x]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (integrable_chi_mul_exp (ξ - b)) (integrable_chi_mul_exp (ξ + b)),
      integral_chi_mul_exp (ξ - b), integral_chi_mul_exp (ξ + b)]
    push_cast
    ring
  have hsubst : (∫ w : ℝ³, Complex.exp (-(Complex.I * (inner ℝ ξ w : ℂ))) *
        ((chi (σ + w) * Real.cos (inner ℝ b (σ + w)) : ℝ) : ℂ))
      = ∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ ξ (x - σ) : ℂ))) *
          ((chi x * Real.cos (inner ℝ b x) : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ ξ (y - σ) : ℂ))) *
        ((chi y * Real.cos (inner ℝ b y) : ℝ) : ℂ)) σ]
    apply integral_congr_ae
    filter_upwards with x
    simp only [add_sub_cancel_left]
  rw [hsubst]
  rw [show (∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ ξ (x - σ) : ℂ))) *
        ((chi x * Real.cos (inner ℝ b x) : ℝ) : ℂ))
      = ∫ x : ℝ³, Complex.exp (Complex.I * (inner ℝ ξ σ : ℂ)) *
          (Complex.exp (-(Complex.I * (inner ℝ ξ x : ℂ))) *
            ((chi x * Real.cos (inner ℝ b x) : ℝ) : ℂ)) from by
    apply integral_congr_ae
    filter_upwards with x
    rw [hphase x]
    ring]
  rw [MeasureTheory.integral_const_mul, hcompute]

/-! ## 3c. The dilated Fourier identity -/

theorem cos_scaled_ft {ℓ : ℝ} (hℓ : 0 < ℓ) (q b σ : ℝ³) :
    (∫ d : ℝ³,
        Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) *
          ((chi (σ + ℓ⁻¹ • d) * Real.cos (inner ℝ b (σ + ℓ⁻¹ • d)) : ℝ) : ℂ))
      = (ℓ : ℂ) ^ 3 * (Complex.exp (Complex.I * (inner ℝ (ℓ • q) σ : ℂ)) *
          (((1 / 2 : ℝ) * (profHat (ℓ • q - b) + profHat (ℓ • q + b)) : ℝ) : ℂ)) := by
  rw [integral_eq_smul_integral_comp_smul (g := fun d : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) *
        ((chi (σ + ℓ⁻¹ • d) * Real.cos (inner ℝ b (σ + ℓ⁻¹ • d)) : ℝ) : ℂ)) hℓ]
  rw [show (∫ s : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q (ℓ • s) : ℂ))) *
        ((chi (σ + ℓ⁻¹ • (ℓ • s)) * Real.cos (inner ℝ b (σ + ℓ⁻¹ • (ℓ • s))) : ℝ) : ℂ))
      = ∫ w : ℝ³, Complex.exp (-(Complex.I * (inner ℝ (ℓ • q) w : ℂ))) *
          ((chi (σ + w) * Real.cos (inner ℝ b (σ + w)) : ℝ) : ℂ) from by
    apply integral_congr_ae
    filter_upwards with w
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
    rw [show inner ℝ q (ℓ • w) = inner ℝ (ℓ • q) w from by
      rw [inner_smul_right, inner_smul_left]; simp]]
  rw [cos_translate_ft (ℓ • q) b σ, Complex.real_smul, Complex.ofReal_pow]

/-! ## 3d. Measurability and integrability of the profile -/

lemma profHat_stronglyMeasurable : StronglyMeasurable profHat := by
  have hcont : Continuous (fun pz : ℝ³ × ℝ³ => chi pz.2 * Real.cos (inner ℝ pz.1 pz.2)) :=
    (chi_continuous.comp continuous_snd).mul
      (Real.continuous_cos.comp (continuous_fst.inner continuous_snd))
  exact hcont.stronglyMeasurable.integral_prod_right' (ν := volume)

/-- Integrability of the `symD` integrand: `F ‖·‖` is assumed integrable and `profHat` is
bounded by `∫|χ|`. -/
lemma integrable_symD_kern {ℓ : ℝ} {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) (v : ℝ³) :
    Integrable (fun p : ℝ³ => F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (v - p))) volume := by
  obtain ⟨p₀⟩ : Nonempty ℝ³ := inferInstance
  have hC0 : 0 ≤ ∫ z : ℝ³, |chi z| := le_trans (abs_nonneg _) (profHat_abs_le p₀)
  have hg : Integrable (fun p : ℝ³ => ‖F ‖p‖‖ * ((∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|)))
      volume := hFi.norm.mul_const _
  refine hg.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ³ => F ‖p‖) volume := hFi.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ³ => profHat (ℓ • p)) volume :=
      (profHat_stronglyMeasurable.comp_measurable
        (measurable_id.const_smul ℓ)).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : ℝ³ => profHat (ℓ • (v - p))) volume :=
      (profHat_stronglyMeasurable.comp_measurable
        ((measurable_const.sub measurable_id).const_smul ℓ)).aestronglyMeasurable
    exact (h1.mul h2).mul h3
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h2 : |profHat (ℓ • p)| ≤ ∫ z : ℝ³, |chi z| := profHat_abs_le _
    have h3 : |profHat (ℓ • (v - p))| ≤ ∫ z : ℝ³, |chi z| := profHat_abs_le _
    have hC : 0 ≤ ∫ z : ℝ³, |chi z| := hC0
    calc |F ‖p‖| * |profHat (ℓ • p)| * |profHat (ℓ • (v - p))|
        = |F ‖p‖| * (|profHat (ℓ • p)| * |profHat (ℓ • (v - p))|) := by ring
      _ ≤ |F ‖p‖| * ((∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (abs_nonneg _) hC) (abs_nonneg _)
      _ = ‖F ‖p‖‖ * ((∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|)) := by rw [Real.norm_eq_abs]

/-- **The `symD` integrand with the symmetrised profile is `symD`.** -/
theorem symD_half_sum {ℓ : ℝ} {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) (q : ℝ³) :
    (∫ p : ℝ³,
        F ‖p‖ * profHat (ℓ • p) * ((1 / 2 : ℝ) * (profHat (ℓ • (q - p)) + profHat (ℓ • (q + p)))))
      = symD ℓ F q := by
  have hA : Integrable (fun p : ℝ³ => F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))) volume :=
    integrable_symD_kern hFi q
  have hB : Integrable (fun p : ℝ³ => F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q + p))) volume := by
    refine (integrable_symD_kern (ℓ := ℓ) (F := F) hFi (-q)).congr
      (ae_of_all _ (fun p => ?_))
    show F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (-q - p))
      = F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q + p))
    rw [show -q - p = -(q + p) from by abel]
    rw [show ℓ • (-(q + p)) = -(ℓ • (q + p)) from by module, profHat_even]
  rw [symD]
  rw [show (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        ((1 / 2 : ℝ) * (profHat (ℓ • (q - p)) + profHat (ℓ • (q + p)))))
      = ∫ p : ℝ³, ((1 / 2) * (F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p)))
          + (1 / 2) * (F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q + p)))) from by
    apply integral_congr_ae
    filter_upwards with p
    simp only [sub_eq_add_neg]
    ring]
  rw [MeasureTheory.integral_add (hA.const_mul _) (hB.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hsym : (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q + p)))
      = ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p)) := by
    rw [← MeasureTheory.integral_neg_eq_self
      (fun p : ℝ³ => F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q + p))) volume]
    apply integral_congr_ae
    filter_upwards with p
    simp only [norm_neg, sub_eq_add_neg]
    rw [show ℓ • (-p) = -(ℓ • p) from by module, profHat_even]
  rw [hsym]
  ring

/-! ## 4. Continuity and integrability of the triple integrand -/

/-- The set integral over the unit box against the indicator `boxInd`. -/
lemma setIntegral_acube_one_eq (f : ℝ³ → ℂ) :
    (∫ s in acube 1, f s) = ∫ s : ℝ³, ((boxInd s : ℝ) : ℂ) * f s := by
  rw [← MeasureTheory.integral_indicator (acube_measurable 1) (f := f)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ acube 1
  · rw [Set.indicator_of_mem hs, boxInd_of_mem hs, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem hs, boxInd_of_notMem hs, Complex.ofReal_zero, zero_mul]

private lemma continuous_exp_neg_inner (q : ℝ³) :
    Continuous (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))) := by
  apply Complex.continuous_exp.comp
  apply Continuous.neg
  apply Continuous.mul continuous_const
  exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)

lemma measurable_boxInd : Measurable boxInd := by
  rw [boxInd]
  exact measurable_const.indicator (acube_measurable 1)

/-- The `d`-integrand of the `kinFT (bsKern ℓ F)` computation, as a function of `(d, (s, p))`. -/
private noncomputable def kernTriple (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (z : ℝ³ × (ℝ³ × ℝ³)) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ q z.1 : ℂ))) * Complex.ofReal (F ‖z.2.2‖) *
    Complex.ofReal (profHat (ℓ • z.2.2)) * Complex.ofReal (boxInd z.2.1) *
    Complex.ofReal (chi (z.2.1 + ℓ⁻¹ • z.1) *
      Real.cos (inner ℝ (ℓ • z.2.2) (z.2.1 + ℓ⁻¹ • z.1)))

/-- The mass of the bump, used as the bound for `profHat`. -/
private noncomputable def chiMass : ℝ := ∫ w : ℝ³, |chi w|

/-- The dominating function for `kernTriple`. -/
private noncomputable def kernDom (ℓ : ℝ) (F : ℝ → ℝ) (z : ℝ³ × (ℝ³ × ℝ³)) : ℝ :=
  (Metric.closedBall (0 : ℝ³) (3 * ℓ / 2)).indicator
      (fun _ => ((Real.sqrt chiNormSq)⁻¹ * chiMass)) z.1 *
    (boxInd z.2.1 * ‖F ‖z.2.2‖‖)

private lemma kernTriple_norm_eq (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (z : ℝ³ × (ℝ³ × ℝ³)) :
    ‖kernTriple ℓ F q z‖
      = |F ‖z.2.2‖| * |profHat (ℓ • z.2.2)| * |boxInd z.2.1| * |chi (z.2.1 + ℓ⁻¹ • z.1)| *
          |Real.cos (inner ℝ (ℓ • z.2.2) (z.2.1 + ℓ⁻¹ • z.1))| := by
  have hexp : ‖Complex.exp (-(Complex.I * (inner ℝ q z.1 : ℂ)))‖ = 1 := by
    have h : -(Complex.I * (inner ℝ q z.1 : ℂ)) = ((-(inner ℝ q z.1) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  simp only [kernTriple, norm_mul, hexp, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  ring

private lemma kernTriple_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) (q : ℝ³)
    (z : ℝ³ × (ℝ³ × ℝ³)) :
    ‖kernTriple ℓ F q z‖ ≤ kernDom ℓ F z := by
  have hCχ0 : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := le_trans (abs_nonneg _) (abs_chi_le 0)
  have hCp0 : 0 ≤ chiMass := by
    rw [chiMass]; exact le_trans (abs_nonneg _) (profHat_abs_le 0)
  rw [kernTriple_norm_eq]
  unfold kernDom chiMass
  by_cases hs : z.2.1 ∈ acube 1
  · rw [boxInd_of_mem hs, abs_one, mul_one]
    by_cases hd : ‖z.1‖ ≤ 3 * ℓ / 2
    · rw [Set.indicator_of_mem (by rw [Metric.mem_closedBall, dist_zero_right]; exact hd)]
      have hchi : |chi (z.2.1 + ℓ⁻¹ • z.1)| ≤ (Real.sqrt chiNormSq)⁻¹ := abs_chi_le _
      have hprof : |profHat (ℓ • z.2.2)| ≤ ∫ w : ℝ³, |chi w| := profHat_abs_le _
      have hcos : |Real.cos (inner ℝ (ℓ • z.2.2) (z.2.1 + ℓ⁻¹ • z.1))| ≤ 1 :=
        Real.abs_cos_le_one _
      calc |F ‖z.2.2‖| * |profHat (ℓ • z.2.2)| * |chi (z.2.1 + ℓ⁻¹ • z.1)| *
            |Real.cos (inner ℝ (ℓ • z.2.2) (z.2.1 + ℓ⁻¹ • z.1))|
          ≤ |F ‖z.2.2‖| * (∫ w : ℝ³, |chi w|) * (Real.sqrt chiNormSq)⁻¹ * 1 := by
            gcongr
        _ = ((Real.sqrt chiNormSq)⁻¹ * (∫ w : ℝ³, |chi w|)) * (1 * ‖F ‖z.2.2‖‖) := by
            rw [Real.norm_eq_abs]; ring
    · rw [Set.indicator_of_notMem (by
        intro hmem
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hd hmem)]
      have hz : chi (z.2.1 + ℓ⁻¹ • z.1) = 0 :=
        chi_shift_eq_zero_of_gt hℓ hs (lt_of_not_ge hd)
      rw [hz]
      simp
  · rw [boxInd_of_notMem hs]
    simp

lemma integrable_kernTriple {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) (q : ℝ³) :
    Integrable (kernTriple ℓ F q) (volume.prod (volume.prod volume)) := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℝ³) (3 * ℓ / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall 0 _).measure_lt_top⟩
  have hd1 : Integrable (fun d : ℝ³ => (Metric.closedBall (0 : ℝ³) (3 * ℓ / 2)).indicator
      (fun _ => ((Real.sqrt chiNormSq)⁻¹ * chiMass)) d) volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    exact integrable_const _
  have hd2 : Integrable (fun y : ℝ³ × ℝ³ => boxInd y.1 * ‖F ‖y.2‖‖) (volume.prod volume) :=
    integrable_boxInd.mul_prod hFi.norm
  have hdom : Integrable (kernDom ℓ F) (volume.prod (volume.prod volume)) := by
    refine (hd1.mul_prod hd2).congr (ae_of_all _ (fun z => ?_))
    simp only [kernDom, Real.norm_eq_abs]
  refine hdom.mono' ?_ ?_
  · have hFm : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) => F ‖z.2.2‖)
        (volume.prod (volume.prod volume)) := by
      have hqp : Measure.QuasiMeasurePreserving (fun z : ℝ³ × (ℝ³ × ℝ³) => z.2.2)
          (volume.prod (volume.prod volume)) volume :=
        (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).comp
          (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume.prod volume))
      simpa only [Function.comp_def] using
        (hFi.aestronglyMeasurable.comp_quasiMeasurePreserving hqp)
    have hFc : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) => Complex.ofReal (F ‖z.2.2‖))
        (volume.prod (volume.prod volume)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hFm
    have hbm : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) => Complex.ofReal (boxInd z.2.1))
        (volume.prod (volume.prod volume)) := by
      refine Complex.continuous_ofReal.comp_aestronglyMeasurable ?_
      exact (measurable_boxInd.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable
    have hpm : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) =>
        Complex.ofReal (profHat (ℓ • z.2.2))) (volume.prod (volume.prod volume)) := by
      refine Complex.continuous_ofReal.comp_aestronglyMeasurable ?_
      exact (profHat_stronglyMeasurable.comp_measurable
        ((measurable_snd.comp measurable_snd).const_smul ℓ)).aestronglyMeasurable
    have hcont : Continuous (fun z : ℝ³ × (ℝ³ × ℝ³) =>
        chi (z.2.1 + ℓ⁻¹ • z.1) *
          Real.cos (inner ℝ (ℓ • z.2.2) (z.2.1 + ℓ⁻¹ • z.1))) := by
      apply Continuous.mul
      · exact chi_continuous.comp (by fun_prop)
      · refine Real.continuous_cos.comp ?_
        exact Continuous.inner ((continuous_snd.comp continuous_snd).const_smul ℓ) (by fun_prop)
    have hcm : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) =>
        Complex.ofReal (chi (z.2.1 + ℓ⁻¹ • z.1) *
          Real.cos (inner ℝ (ℓ • z.2.2) (z.2.1 + ℓ⁻¹ • z.1))))
        (volume.prod (volume.prod volume)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hcont.aestronglyMeasurable
    have hexp : AEStronglyMeasurable (fun z : ℝ³ × (ℝ³ × ℝ³) =>
        Complex.exp (-(Complex.I * (inner ℝ q z.1 : ℂ)))) (volume.prod (volume.prod volume)) :=
      ((continuous_exp_neg_inner q).comp continuous_fst).aestronglyMeasurable
    have hprod : AEStronglyMeasurable (kernTriple ℓ F q) (volume.prod (volume.prod volume)) :=
      ((((hexp.mul hFc).mul hpm).mul hbm).mul hcm)
    simpa only [kernTriple] using hprod
  · filter_upwards with z
    exact kernTriple_norm_le hℓ F q z

/-! ## 5. The target theorem -/

/-- The `d`-integrand after the phase has been pulled inside the `p`-integral. -/
private noncomputable def kernPull (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (d s p : ℝ³) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) *
    (((boxInd s : ℝ) : ℂ) *
      Complex.ofReal (F ‖p‖ * profHat (ℓ • p) *
        (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d)))))

private lemma kernTriple_eq_kernPull (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (d s p : ℝ³) :
    kernTriple ℓ F q (d, (s, p)) = kernPull ℓ F q d s p := by
  simp only [kernTriple, kernPull, Complex.ofReal_mul]
  ring

/-- The `p`-integral of `kernPull` with the constants pulled out. -/
private lemma integral_kernPull (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (d s : ℝ³) :
    (∫ p : ℝ³, kernPull ℓ F q d s p)
      = Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) *
          (((boxInd s : ℝ) : ℂ) * ∫ p : ℝ³, Complex.ofReal (F ‖p‖ * profHat (ℓ • p) *
            (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d))))) := by
  simp only [kernPull]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The `d`-integrand with the `d`-dependence isolated in the second factor. -/
private noncomputable def kernSplit (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (d s p : ℝ³) : ℂ :=
  (((boxInd s : ℝ) : ℂ) * Complex.ofReal (F ‖p‖) * Complex.ofReal (profHat (ℓ • p))) *
    (Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) *
      Complex.ofReal (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d))))

private lemma kernTriple_eq_kernSplit (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (d s p : ℝ³) :
    kernTriple ℓ F q (d, (s, p)) = kernSplit ℓ F q d s p := by
  simp only [kernTriple, kernSplit]
  ring

/-- The pointwise value of the inner `d`-integral. -/
private noncomputable def kernG (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (y : ℝ³ × ℝ³) : ℂ :=
  ((boxInd y.1 : ℝ) : ℂ) * (Complex.exp (Complex.I * (inner ℝ (ℓ • q) y.1 : ℂ)) *
    ((ℓ : ℂ) ^ 3 * Complex.ofReal (F ‖y.2‖ * profHat (ℓ • y.2) *
      ((1 / 2 : ℝ) * (profHat (ℓ • (q - y.2)) + profHat (ℓ • (q + y.2)))))))

private lemma kernG_factor (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) (s p : ℝ³) :
    kernG ℓ F q (s, p) =
      (((boxInd s : ℝ) : ℂ) * Complex.exp (Complex.I * (inner ℝ (ℓ • q) s : ℂ))) *
        ((ℓ : ℂ) ^ 3 * Complex.ofReal (F ‖p‖ * profHat (ℓ • p) *
          ((1 / 2 : ℝ) * (profHat (ℓ • (q - p)) + profHat (ℓ • (q + p)))))) := by
  simp only [kernG]
  ring

private lemma integral_kernTriple_eq_kernG {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (q : ℝ³) (y : ℝ³ × ℝ³) :
    (∫ d : ℝ³, kernTriple ℓ F q (d, y)) = kernG ℓ F q y := by
  obtain ⟨s, p⟩ := y
  rw [show (∫ d : ℝ³, kernTriple ℓ F q (d, (s, p))) = ∫ d : ℝ³, kernSplit ℓ F q d s p from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with d
    exact kernTriple_eq_kernSplit ℓ F q d s p]
  rw [show (∫ d : ℝ³, kernSplit ℓ F q d s p)
        = (((boxInd s : ℝ) : ℂ) * Complex.ofReal (F ‖p‖) * Complex.ofReal (profHat (ℓ • p))) *
            ∫ d : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) *
              Complex.ofReal (chi (s + ℓ⁻¹ • d) *
                Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d))) from by
    simp only [kernSplit]
    rw [MeasureTheory.integral_const_mul]]
  rw [cos_scaled_ft hℓ q (ℓ • p) s]
  rw [show (((boxInd s : ℝ) : ℂ) * Complex.ofReal (F ‖p‖) * Complex.ofReal (profHat (ℓ • p))) *
        ((ℓ : ℂ) ^ 3 * (Complex.exp (Complex.I * (inner ℝ (ℓ • q) s : ℂ)) *
          Complex.ofReal ((1 / 2 : ℝ) * (profHat (ℓ • q - ℓ • p) + profHat (ℓ • q + ℓ • p)))))
      = kernG ℓ F q (s, p) from by
    rw [← smul_sub, ← smul_add]
    simp only [kernG, Complex.ofReal_mul]
    ring]

theorem kinFT_bsKern {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (q : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun d : EuclideanSpace ℝ (Fin 3) => (Work.OneBodyKin.bsKern ℓ F d : ℂ)) q
      = (Work.OneBodyKin.boxHat ℓ q : ℂ) * (Work.OneBodyKin.symD ℓ F q : ℂ) := by
  have hKer : Integrable (kernTriple ℓ F q) (volume.prod (volume.prod volume)) :=
    integrable_kernTriple hℓ hFi q
  -- ### Step 0: the cast of `bsKern` as a `boxInd`-weighted double integral
  have hcast : ∀ d : ℝ³, ((bsKern ℓ F d : ℝ) : ℂ)
      = ∫ s : ℝ³, ((boxInd s : ℝ) : ℂ) *
          (∫ p : ℝ³, ((F ‖p‖ * profHat (ℓ • p) *
            (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d))) : ℝ) : ℂ)) := by
    intro d
    have h1 : ((bsKern ℓ F d : ℝ) : ℂ)
        = ∫ s in acube 1, ((∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
            (chi (s + ℓ⁻¹ • d) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • d))) : ℝ) : ℂ) := by
      rw [bsKern]
      exact (integral_complex_ofReal).symm
    rw [h1, setIntegral_acube_one_eq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    rw [integral_complex_ofReal]
  -- ### Step 1: unfold `kinFT`, insert the phase and expose the triple integral
  rw [Submission.BoseGases.kinFT]
  have h2 : (∫ d : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q d : ℂ))) * ((bsKern ℓ F d : ℝ) : ℂ))
      = ∫ d : ℝ³, ∫ s : ℝ³, ∫ p : ℝ³, kernTriple ℓ F q (d, (s, p)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with d
    rw [hcast d, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p : ℝ³ => kernTriple_eq_kernPull ℓ F q d s p))]
    rw [integral_kernPull ℓ F q d s]
  rw [h2]
  -- ### Step 2: Fubini on `(s, p)` and then swap `d` with the pair
  have h3 : (∫ d : ℝ³, ∫ s : ℝ³, ∫ p : ℝ³, kernTriple ℓ F q (d, (s, p)))
      = ∫ y : ℝ³ × ℝ³, ∫ d : ℝ³, kernTriple ℓ F q (d, y) := by
    rw [show (∫ d : ℝ³, ∫ s : ℝ³, ∫ p : ℝ³, kernTriple ℓ F q (d, (s, p)))
          = ∫ d : ℝ³, ∫ y : ℝ³ × ℝ³, kernTriple ℓ F q (d, y) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hKer.prod_right_ae] with d hd
      exact MeasureTheory.integral_integral (f := fun s p => kernTriple ℓ F q (d, (s, p))) hd]
    exact MeasureTheory.integral_integral_swap (f := fun d y => kernTriple ℓ F q (d, y)) hKer
  rw [h3]
  -- ### Step 3: the inner `d`-integral, pointwise in `y = (s, p)`
  have hH : Integrable (fun y : ℝ³ × ℝ³ => ∫ d : ℝ³, kernTriple ℓ F q (d, y))
      (volume.prod volume) := by
    have h := (hKer.swap).integral_prod_left
    simpa using h
  have hGint : Integrable (kernG ℓ F q) (volume.prod volume) :=
    hH.congr (ae_of_all _ (fun y => integral_kernTriple_eq_kernG hℓ q y))
  rw [show (∫ y : ℝ³ × ℝ³, ∫ d : ℝ³, kernTriple ℓ F q (d, y))
        = ∫ y : ℝ³ × ℝ³, kernG ℓ F q y ∂(volume.prod volume) from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    exact integral_kernTriple_eq_kernG hℓ q y]
  rw [MeasureTheory.integral_prod_symm (f := kernG ℓ F q) hGint]
  -- ### Step 4: pull out the constants
  rw [show (∫ p : ℝ³, ∫ s : ℝ³, kernG ℓ F q (s, p))
        = ∫ p : ℝ³, (∫ s : ℝ³, (((boxInd s : ℝ) : ℂ) *
              Complex.exp (Complex.I * (inner ℝ (ℓ • q) s : ℂ)))) *
            ((ℓ : ℂ) ^ 3 * Complex.ofReal (F ‖p‖ * profHat (ℓ • p) *
              ((1 / 2 : ℝ) * (profHat (ℓ • (q - p)) + profHat (ℓ • (q + p)))))) from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun s : ℝ³ => kernG_factor ℓ F q s p))]
    rw [MeasureTheory.integral_mul_const]]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ s : ℝ³, ((boxInd s : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ (ℓ • q) s : ℂ)))
      = (boxHat 1 (ℓ • q) : ℂ) from by
    rw [← setIntegral_acube_one_eq
      (fun s : ℝ³ => Complex.exp (Complex.I * (inner ℝ (ℓ • q) s : ℂ)))]
    exact integral_exp_box (ℓ • q)]
  rw [show (∫ p : ℝ³, (ℓ : ℂ) ^ 3 * Complex.ofReal (F ‖p‖ * profHat (ℓ • p) *
        ((1 / 2 : ℝ) * (profHat (ℓ • (q - p)) + profHat (ℓ • (q + p))))))
      = (ℓ : ℂ) ^ 3 * (symD ℓ F q : ℂ) from by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [integral_complex_ofReal, symD_half_sum (ℓ := ℓ) hFi q]]
  rw [BoxHat.boxHat_scale hℓ q]
  push_cast
  ring

end Work.OneBodyKin
