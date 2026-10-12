import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.BoseFixB3.Conv.Scale.multOn_scale_phi
import Submission.Work.BoseFixB3.Conv.Tail.kinFT_phiC_tail_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Conv/chi_highpass_decay`

The high-frequency part `(1 − f_L)(χ_Λ²)` of the localisation window is rapidly small:
there is a universal constant `C` with

`|f_L(χ_Λ²)(x) − χ_Λ(x)²| ≤ C / (ℓκ)⁴⁰`

uniformly in the cut-off `fc`, in `κ, ℓ > 0` and in `x`.

Writing `φ = χ²` (the corpus bump squared, `Work.BoseFixB3.Scaling.phi`) the dilation
`χ_Λ(x)² = φ(ℓ⁻¹ • x)` is the profile `φ` rescaled by `ℓ`; the multiplier `f_L` acts on the
frequencies by `f(‖p‖/κ)`, so after the change of variables `p ↦ ℓ⁻¹ p` the *whole* statement
is the `ℓ = 1` statement for `φ` with cut-off `ℓκ`:

`|f_L(φ)(y) − φ(y)| ≤ C (ℓκ)^{-40}`.

In Fourier space, `f_L(φ)^ − φ^ = (f(‖·‖/κ) − 1) φ^` is supported on `‖p‖ ≥ κ` and `φ` is a
Schwartz function, so the difference is bounded by the tail `∫_{‖p‖ ≥ κ} ‖φ̂‖ ≲ κ^{-40}`.

## Contents

* `ChiFourier.lean` — Fourier inversion, Schwartz decay/integrability of `φ̂`.
* `lowMult_eq_multOn` — the definitional identification with the general multiplier `multOn`.
* `lowMult_one_core` — the `ℓ = 1` estimate.
* `chi_highpass_decay` — the target.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform SchwartzMap

namespace Work.BoseFixB3.Conv

open Work.BoseFixB3.Scaling

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### 0. The two analytic inputs (proved in the `Scale`/`Tail` modules) -/

private lemma tail_aux :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      ∫ q in {q : E3 | r ≤ ‖q‖}, ‖Submission.BoseGases.kinFT phiC q‖
        ≤ C * r ^ (-(40:ℝ)) := Tail.kinFT_phiC_tail_le

private lemma scale_aux (F : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : E3) :
    Work.BoseFixB3.multOn F ℓ (fun z => phi (ℓ⁻¹ • z)) x
      = Work.BoseFixB3.multOn (fun r => F (ℓ⁻¹ * r)) 1 phi (ℓ⁻¹ • x) :=
  Scale.multOn_scale_phi F ℓ hℓ x

/-! ### 1. The multiplier vocabulary -/

/-- `lowMult` is the general Fourier multiplier `multOn` with the symbol `fc.f (·/κ)`. -/
lemma lowMult_eq_multOn (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (ψ : E3 → ℝ) (x : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = Work.BoseFixB3.multOn (fun r => fc.f (r / κ)) ℓ ψ x := rfl

/-- The cut-off `f` takes values in `[0,1]`. -/
lemma lowCut_bounds (fc : Work.BoseBoxFix.LowCut) (s : ℝ) :
    0 ≤ fc.f s ∧ fc.f s ≤ 1 := by
  have h2 : fc.f 2 = 0 := fc.zero 2 le_rfl
  have h1 : fc.f 1 = 1 := fc.one 1 le_rfl
  constructor
  · rcases lt_or_ge s 2 with h | h
    · have := fc.anti h.le
      rw [h2] at this; exact this
    · rw [fc.zero s h]
  · rcases lt_or_ge s 1 with h | h
    · rw [fc.one s h.le]
    · have := fc.anti h
      rw [h1] at this; exact this

/-- The indicator of the unit cube is redundant on the profile `φ = χ²`. -/
lemma indicator_phi_unit : (Submission.BoseGases.acube 1).indicator phi = phi := by
  have h2 : (fun z : E3 => Submission.BoseGases.chiU (1:ℝ) 0 z ^ 2) = phi := by
    funext w; simp [Submission.BoseGases.chiU, phi]
  have h : (Submission.BoseGases.acube (1:ℝ)).indicator
      (fun z : E3 => Submission.BoseGases.chiU (1:ℝ) 0 z ^ 2)
      = fun z : E3 => phi ((1:ℝ)⁻¹ • z) :=
    funext fun z => chiU_sq_indicator (1:ℝ) one_pos z
  rw [h2] at h
  simpa using h

/-! ### 2. The `ℓ = 1` core estimate -/

lemma lowMult_one_core :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (μ : ℝ), 0 < μ → ∀ y : E3,
      |Work.BoseBoxFix.lowMult fc μ 1 phi y - phi y| ≤ C * μ ^ (-(40:ℝ)) := by
  obtain ⟨C₁, hC₁, htail⟩ := tail_aux
  refine ⟨((2 * π) ^ 3)⁻¹ * C₁, by positivity, ?_⟩
  intro fc μ hμ y
  have hfc : Continuous fc.f := fc.smooth.continuous
  have hkin : Continuous (Submission.BoseGases.kinFT phiC) := continuous_kinFT_phiC
  have hexpC : Continuous fun p : E3 => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) := by
    fun_prop
  have hexp : ∀ p : E3, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ))‖ = 1 :=
    fun p => Complex.norm_exp_I_mul_ofReal (inner ℝ p y)
  have hcutC : Continuous fun p : E3 => ((fc.f (‖p‖ / μ) : ℝ) : ℂ) := by fun_prop
  have hcut1C : Continuous fun p : E3 => ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) := by fun_prop
  -- integrability of the three integrands
  have h00 : Integrable (fun p : E3 => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      Submission.BoseGases.kinFT phiC p) := by
    refine kinFT_phiC_integrable.norm.mono' (hexpC.mul hkin).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Complex.norm_mul, hexp p, one_mul]
  have h11 : Integrable (fun p : E3 => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      ((fc.f (‖p‖ / μ) : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p) := by
    refine kinFT_phiC_integrable.norm.mono' ((hexpC.mul hcutC).mul hkin).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hb := lowCut_bounds fc (‖p‖ / μ)
    rw [Complex.norm_mul, Complex.norm_mul, hexp p, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hAA : Integrable (fun p : E3 => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p) := by
    refine kinFT_phiC_integrable.norm.mono' ((hexpC.mul hcut1C).mul hkin).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hb := lowCut_bounds fc (‖p‖ / μ)
    have habs : |fc.f (‖p‖ / μ) - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
    rw [Complex.norm_mul, Complex.norm_mul, hexp p, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) habs
  -- `lowMult` as the integral of the first integrand
  have hfun1 : (fun z : E3 => (((Submission.BoseGases.acube 1).indicator phi z : ℝ) : ℂ))
      = phiC := by
    funext z
    rw [indicator_phi_unit]
    rfl
  have hlhs : Work.BoseBoxFix.lowMult fc μ 1 phi y
      = (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
          ((fc.f (‖p‖ / μ) : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p).re := by
    rw [lowMult_eq_multOn fc μ 1 phi y, Work.BoseFixB3.multOn, hfun1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- the inversion value
  have hinv : (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      Submission.BoseGases.kinFT phiC p).re = phi y := by
    have h := kinInv_kinFT_phiC y
    have hre := congrArg Complex.re h
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using hre
  -- the difference is the integral of the third integrand
  have hdiff : (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        ((fc.f (‖p‖ / μ) : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p)
      - (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        Submission.BoseGases.kinFT phiC p)
      = ∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p := by
    rw [← integral_sub h11 h00]
    apply integral_congr_ae
    filter_upwards with p
    push_cast
    ring
  have hkey : Work.BoseBoxFix.lowMult fc μ 1 phi y - phi y
      = (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
          ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p).re := by
    rw [hlhs, ← hinv, ← mul_sub]
    congr 1
    rw [← Complex.sub_re, hdiff]
  -- the effective support of the third integrand
  set s : Set E3 := {p | μ ≤ ‖p‖} with hs
  have hs_meas : MeasurableSet s :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hzero : ∀ p ∉ s, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p = 0 := by
    intro p hp
    simp only [hs, Set.mem_setOf_eq, not_le] at hp
    have hratio : ‖p‖ / μ ≤ 1 := by
      rw [div_le_one hμ]; exact le_of_lt hp
    have hf : fc.f (‖p‖ / μ) = 1 := fc.one _ hratio
    simp [hf]
  have hAnorm_int : Integrable (fun p : E3 => ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖) := hAA.norm
  have hknorm_int : Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT phiC p‖) :=
    kinFT_phiC_integrable.norm
  have hAeq : (∫ p : E3, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖)
      = ∫ p in s, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := s) (μ := volume)
      (fun p hp => by rw [hzero p hp, norm_zero])).symm
  have hAle : (∫ p in s, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖)
      ≤ ∫ p in s, ‖Submission.BoseGases.kinFT phiC p‖ := by
    apply setIntegral_mono_on hAnorm_int.integrableOn hknorm_int.integrableOn hs_meas
    intro p _
    have hb := lowCut_bounds fc (‖p‖ / μ)
    have habs : |fc.f (‖p‖ / μ) - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
    rw [Complex.norm_mul, Complex.norm_mul, hexp p, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) habs
  have htailμ : ∫ p in s, ‖Submission.BoseGases.kinFT phiC p‖ ≤ C₁ * μ ^ (-(40:ℝ)) :=
    htail μ hμ
  have hnormA : ‖∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
      ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖
      ≤ ∫ p : E3, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖ :=
    norm_integral_le_integral_norm _
  -- final chain
  have hc : (0:ℝ) ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  calc |Work.BoseBoxFix.lowMult fc μ 1 phi y - phi y|
      = (((2 * π) ^ 3)⁻¹ : ℝ) *
          |(∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
            ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p).re| := by
        rw [hkey, abs_mul, abs_of_nonneg hc]
    _ ≤ (((2 * π) ^ 3)⁻¹ : ℝ) *
          ‖∫ p : E3, Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
            ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc
    _ ≤ (((2 * π) ^ 3)⁻¹ : ℝ) *
          ∫ p : E3, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
            ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖ :=
        mul_le_mul_of_nonneg_left hnormA hc
    _ = (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p in s, ‖Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
            ((fc.f (‖p‖ / μ) - 1 : ℝ) : ℂ) * Submission.BoseGases.kinFT phiC p‖) := by
        rw [hAeq]
    _ ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (∫ p in s, ‖Submission.BoseGases.kinFT phiC p‖) :=
        mul_le_mul_of_nonneg_left hAle hc
    _ ≤ (((2 * π) ^ 3)⁻¹ : ℝ) * (C₁ * μ ^ (-(40:ℝ))) :=
        mul_le_mul_of_nonneg_left htailμ hc
    _ = (((2 * π) ^ 3)⁻¹ * C₁) * μ ^ (-(40:ℝ)) := by ring

/-! ### 3. The target -/

theorem chi_highpass_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ),
      0 < ℓ → 0 < κ → ∀ x : EuclideanSpace ℝ (Fin 3),
        |Work.BoseBoxFix.lowMult fc κ ℓ (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z) ^ 2) x
          - Submission.BoseGases.chi ((ℓ⁻¹) • x) ^ 2| ≤ C / (ℓ * κ) ^ 40 := by
  obtain ⟨C, hC, hcore⟩ := lowMult_one_core
  refine ⟨C, hC, ?_⟩
  intro fc κ ℓ hℓ hκ x
  have hfun : (fun z : E3 => Submission.BoseGases.chi (ℓ⁻¹ • z) ^ 2)
      = fun z : E3 => phi (ℓ⁻¹ • z) := by
    funext z; simp [phi]
  rw [hfun]
  have hscale := scale_aux (fun r => fc.f (r / κ)) ℓ hℓ x
  have hFeq : (fun r : ℝ => fc.f ((ℓ⁻¹) * r / κ)) = fun r : ℝ => fc.f (r / (ℓ * κ)) := by
    funext r
    congr 1
    field_simp
  have hstep : Work.BoseBoxFix.lowMult fc κ ℓ (fun z : E3 => phi (ℓ⁻¹ • z)) x
      = Work.BoseBoxFix.lowMult fc (ℓ * κ) 1 phi (ℓ⁻¹ • x) := by
    rw [lowMult_eq_multOn fc κ ℓ _ x, hscale, hFeq]
    exact (lowMult_eq_multOn fc (ℓ * κ) 1 phi (ℓ⁻¹ • x)).symm
  rw [hstep]
  have hphi : phi (ℓ⁻¹ • x) = Submission.BoseGases.chi (ℓ⁻¹ • x) ^ 2 := by simp [phi]
  rw [← hphi]
  calc |Work.BoseBoxFix.lowMult fc (ℓ * κ) 1 phi (ℓ⁻¹ • x) - phi (ℓ⁻¹ • x)|
      ≤ C * (ℓ * κ) ^ (-(40:ℝ)) := hcore fc (ℓ * κ) (by positivity) (ℓ⁻¹ • x)
    _ = C / (ℓ * κ) ^ 40 := by
        rw [div_eq_mul_inv]
        congr 1
        rw [Real.rpow_neg (by positivity)]
        exact congrArg Inv.inv (Real.rpow_natCast (ℓ * κ) 40)

end Work.BoseFixB3.Conv
