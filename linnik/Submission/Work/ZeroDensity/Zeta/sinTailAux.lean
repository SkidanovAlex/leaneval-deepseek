import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeSelf.oscillatoryIoiBound

namespace Work.ZeroDensity.Zeta.SinAux

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-! ### Complex powers of positive reals -/

lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, show r * r = r ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs r

lemma cpow_ofReal_eq (v : ℝ) (hv : 0 < v) (c : ℂ) :
    (v : ℂ) ^ c = Complex.exp (c * ((Real.log v : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hv)),
      (Complex.ofReal_log (le_of_lt hv)).symm, mul_comm]

lemma inv_eq_exp_neg_log {v : ℝ} (hv : 0 < v) :
    (v : ℂ)⁻¹ = Complex.exp (-((Real.log v : ℝ) : ℂ)) := by
  rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hv]

lemma norm_exp_I_mul (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (x : ℂ), Complex.norm_exp_ofReal_mul_I]

/-! ### Phase form of the oscillating integrand -/

lemma cpow_exp_I_phase (t v : ℝ) (hv : 0 < v) :
    (v : ℂ) ^ (-(1/2 : ℂ) - (t : ℂ) * Complex.I) * Complex.exp (Complex.I * (v : ℂ))
      = ((Real.rpow v (-(1/2)) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((v - t * Real.log v : ℝ) : ℂ)) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  have hlog : Complex.log (v : ℂ) = ((Real.log v : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hv)).symm
  have hrpow : ((Real.rpow v (-(1/2)) : ℝ) : ℂ)
      = Complex.exp (((Real.log v : ℝ) : ℂ) * (-(1/2))) := by
    rw [show Real.rpow v (-(1/2)) = Real.exp (Real.log v * (-(1/2))) from
      Real.rpow_def_of_pos hv (-(1/2)), Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hv0, hlog, hrpow, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cpow_exp_negI_phase (t v : ℝ) (hv : 0 < v) :
    (v : ℂ) ^ (-(1/2 : ℂ) - (t : ℂ) * Complex.I) * Complex.exp (-(Complex.I * (v : ℂ)))
      = ((Real.rpow v (-(1/2)) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-v - t * Real.log v) : ℝ) : ℂ)) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  have hlog : Complex.log (v : ℂ) = ((Real.log v : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt hv)).symm
  have hrpow : ((Real.rpow v (-(1/2)) : ℝ) : ℂ)
      = Complex.exp (((Real.log v : ℝ) : ℂ) * (-(1/2))) := by
    rw [show Real.rpow v (-(1/2)) = Real.exp (Real.log v * (-(1/2))) from
      Real.rpow_def_of_pos hv (-(1/2)), Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hv0, hlog, hrpow, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The exponent `-1/2 - it` -/

/-- The complex exponent `-(1/2) - it`. -/
def ct (t : ℝ) : ℂ := -(1/2 : ℂ) - (t : ℂ) * Complex.I

lemma ct_ne_zero (t : ℝ) : ct t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.zero_re] at hre
  simp [ct] at hre

lemma ct_im (t : ℝ) : (ct t).im = -t := by simp [ct]

lemma ct_re (t : ℝ) : (ct t).re = -(1/2) := by simp [ct]

lemma ct_sub_one_re (t : ℝ) : (ct t - 1).re = -(3/2) := by
  rw [Complex.sub_re, ct_re, Complex.one_re]
  norm_num

lemma le_norm_ct {t : ℝ} (ht : 0 ≤ t) : t ≤ ‖ct t‖ := by
  have h := Complex.abs_im_le_norm (ct t)
  rwa [ct_im, abs_neg, abs_of_nonneg ht] at h

/-! ### Auxiliary exponential functions -/

/-- Antiderivative candidate for `v^{-1/2-it} e^{iv}`. -/
def Gp (c : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (c * ((Real.log v : ℝ) : ℂ) + Complex.I * (v : ℂ))

/-- Antiderivative candidate for `v^{-1/2-it} e^{-iv}`. -/
def Gm (c : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (c * ((Real.log v : ℝ) : ℂ) - Complex.I * (v : ℂ))

def Fp (c : ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((c - 1) * ((Real.log v : ℝ) : ℂ) + Complex.I * (v : ℂ))

def Fm (c : ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((c - 1) * ((Real.log v : ℝ) : ℂ) - Complex.I * (v : ℂ))

lemma hasDerivAt_Gp (c : ℂ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (Gp c) (Gp c v * (c * (v : ℂ)⁻¹ + Complex.I)) v := by
  unfold Gp
  have hl : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) (((v : ℝ)⁻¹ : ℝ) : ℂ) v :=
    (Real.hasDerivAt_log hv).ofReal_comp
  have hi : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 v := by
    simpa using (hasDerivAt_id (v : ℝ)).ofReal_comp
  have h := ((hl.const_mul c).add (hi.const_mul Complex.I)).cexp
  have heq : ((fun y : ℝ => c * ((Real.log y : ℝ) : ℂ)) + fun y : ℝ => (Complex.I * ((y : ℝ) : ℂ)))
      = (fun y : ℝ => c * ((Real.log y : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)) := rfl
  rw [heq] at h
  convert h using 1
  rw [Complex.ofReal_inv]
  ring

lemma hasDerivAt_Gm (c : ℂ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (Gm c) (Gm c v * (c * (v : ℂ)⁻¹ - Complex.I)) v := by
  unfold Gm
  have hl : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) (((v : ℝ)⁻¹ : ℝ) : ℂ) v :=
    (Real.hasDerivAt_log hv).ofReal_comp
  have hi : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 v := by
    simpa using (hasDerivAt_id (v : ℝ)).ofReal_comp
  have h := ((hl.const_mul c).sub (hi.const_mul Complex.I)).cexp
  have heq : ((fun y : ℝ => c * ((Real.log y : ℝ) : ℂ)) - fun y : ℝ => (Complex.I * ((y : ℝ) : ℂ)))
      = (fun y : ℝ => c * ((Real.log y : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)) := rfl
  rw [heq] at h
  convert h using 1
  rw [Complex.ofReal_inv]
  ring

lemma Fp_eq_Gp (c : ℂ) {v : ℝ} (hv : 0 < v) : Fp c v = Gp c v * (v : ℂ)⁻¹ := by
  have hinv := inv_eq_exp_neg_log hv
  unfold Fp Gp
  rw [hinv, ← Complex.exp_add]
  congr 1
  ring

lemma Fm_eq_Gm (c : ℂ) {v : ℝ} (hv : 0 < v) : Fm c v = Gm c v * (v : ℂ)⁻¹ := by
  have hinv := inv_eq_exp_neg_log hv
  unfold Fm Gm
  rw [hinv, ← Complex.exp_add]
  congr 1
  ring

lemma Gp_deriv_id (c : ℂ) {v : ℝ} (hv : 0 < v) :
    Gp c v * (c * (v : ℂ)⁻¹ + Complex.I) = c * Fp c v + Complex.I * Gp c v := by
  rw [Fp_eq_Gp c hv]; ring

lemma Gm_deriv_id (c : ℂ) {v : ℝ} (hv : 0 < v) :
    Gm c v * (c * (v : ℂ)⁻¹ - Complex.I) = c * Fm c v - Complex.I * Gm c v := by
  rw [Fm_eq_Gm c hv]; ring

lemma Gp_eq_cpow (c : ℂ) {v : ℝ} (hv : 0 < v) :
    Gp c v = (v : ℂ) ^ c * Complex.exp (Complex.I * (v : ℂ)) := by
  rw [show (v : ℂ) ^ c = Complex.exp (c * ((Real.log v : ℝ) : ℂ)) from cpow_ofReal_eq v hv c,
      ← Complex.exp_add]
  unfold Gp
  ring

lemma Gm_eq_cpow (c : ℂ) {v : ℝ} (hv : 0 < v) :
    Gm c v = (v : ℂ) ^ c * Complex.exp (-(Complex.I * (v : ℂ))) := by
  rw [show (v : ℂ) ^ c = Complex.exp (c * ((Real.log v : ℝ) : ℂ)) from cpow_ofReal_eq v hv c,
      ← Complex.exp_add]
  unfold Gm
  ring

lemma Fp_eq_cpow (c : ℂ) {v : ℝ} (hv : 0 < v) :
    Fp c v = (v : ℂ) ^ (c - 1) * Complex.exp (Complex.I * (v : ℂ)) := by
  rw [show (v : ℂ) ^ (c - 1) = Complex.exp ((c - 1) * ((Real.log v : ℝ) : ℂ)) from
        cpow_ofReal_eq v hv (c - 1), ← Complex.exp_add]
  unfold Fp
  ring

lemma Fm_eq_cpow (c : ℂ) {v : ℝ} (hv : 0 < v) :
    Fm c v = (v : ℂ) ^ (c - 1) * Complex.exp (-(Complex.I * (v : ℂ))) := by
  rw [show (v : ℂ) ^ (c - 1) = Complex.exp ((c - 1) * ((Real.log v : ℝ) : ℂ)) from
        cpow_ofReal_eq v hv (c - 1), ← Complex.exp_add]
  unfold Fm
  ring

lemma norm_Gp_ct (t : ℝ) {v : ℝ} (hv : 0 < v) :
    ‖Gp (ct t) v‖ = v ^ (-(1/2) : ℝ) := by
  rw [Gp_eq_cpow (ct t) hv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, ct_re,
      norm_exp_I_mul v, mul_one]

lemma norm_Gm_ct (t : ℝ) {v : ℝ} (hv : 0 < v) :
    ‖Gm (ct t) v‖ = v ^ (-(1/2) : ℝ) := by
  rw [Gm_eq_cpow (ct t) hv, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, ct_re]
  have : ‖Complex.exp (-(Complex.I * (v : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [this, mul_one]

lemma Gp_mul_eq (t : ℝ) {v : ℝ} (hv : 0 < v) :
    (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)) * (ct t * (v : ℂ)⁻¹ + Complex.I)
      = ct t * ((v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
        + Complex.I * ((v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ))) := by
  rw [← Gp_eq_cpow (ct t) hv, ← Fp_eq_cpow (ct t) hv, Gp_deriv_id (ct t) hv]

lemma Gm_mul_eq (t : ℝ) {v : ℝ} (hv : 0 < v) :
    (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))) * (ct t * (v : ℂ)⁻¹ - Complex.I)
      = ct t * ((v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))
        - Complex.I * ((v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ)))) := by
  rw [← Gm_eq_cpow (ct t) hv, ← Fm_eq_cpow (ct t) hv, Gm_deriv_id (ct t) hv]

/-! ### The sine as a difference of two exponentials -/

lemma sin_eq_exp (v : ℝ) : ((Real.sin v : ℝ) : ℂ)
    = (1 / (2 * Complex.I)) *
        (Complex.exp (Complex.I * (v : ℂ)) - Complex.exp (-(Complex.I * (v : ℂ)))) := by
  rw [Complex.ofReal_sin, Complex.sin]
  rw [show -(↑v : ℂ) * Complex.I = -(Complex.I * ↑v) by ring]
  rw [show (↑v : ℂ) * Complex.I = Complex.I * ↑v by ring]
  field_simp
  simp only [pow_two, Complex.I_mul_I]
  ring

lemma sin_mul_cpow_split (e : ℂ) (v : ℝ) :
    ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ e
      = (1 / (2 * Complex.I)) * ((v : ℂ) ^ e * Complex.exp (Complex.I * (v : ℂ))
          - (v : ℂ) ^ e * Complex.exp (-(Complex.I * (v : ℂ)))) := by
  rw [sin_eq_exp]
  ring

/-! ### Continuity and interval integrability -/

lemma continuous_exp_I_mul : Continuous (fun v : ℝ => Complex.exp (Complex.I * (v : ℂ))) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

lemma continuous_exp_neg_I_mul :
    Continuous (fun v : ℝ => Complex.exp (-(Complex.I * (v : ℂ)))) :=
  Complex.continuous_exp.comp
    ((continuous_const.mul Complex.continuous_ofReal).neg)

lemma contOn_cpow (c : ℂ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun v : ℝ => (v : ℂ) ^ c) (Set.Ici A) := by
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x c
    (Or.inr (ne_of_gt (lt_of_lt_of_le hA hx)))).continuousWithinAt

lemma contOn_cpow_mul_expI (c : ℂ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun v : ℝ => (v : ℂ) ^ c * Complex.exp (Complex.I * (v : ℂ)))
      (Set.Ici A) :=
  (contOn_cpow c hA).mul continuous_exp_I_mul.continuousOn

lemma contOn_cpow_mul_expNegI (c : ℂ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun v : ℝ => (v : ℂ) ^ c * Complex.exp (-(Complex.I * (v : ℂ))))
      (Set.Ici A) :=
  (contOn_cpow c hA).mul continuous_exp_neg_I_mul.continuousOn

lemma intervalIntegrable_cpow_mul_expI (c k : ℂ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun v : ℝ => k * ((v : ℂ) ^ c * Complex.exp (Complex.I * (v : ℂ))))
      volume A B := by
  have h1 : ContinuousOn (fun v : ℝ => k * ((v : ℂ) ^ c * Complex.exp (Complex.I * (v : ℂ))))
      (Set.Ici A) := continuousOn_const.mul (contOn_cpow_mul_expI c hA)
  exact (h1.mono (by intro x hx; rw [Set.uIcc_of_le hAB] at hx; exact hx.1)).intervalIntegrable

lemma intervalIntegrable_cpow_mul_expNegI (c k : ℂ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun v : ℝ => k * ((v : ℂ) ^ c * Complex.exp (-(Complex.I * (v : ℂ)))))
      volume A B := by
  have h1 : ContinuousOn (fun v : ℝ => k * ((v : ℂ) ^ c * Complex.exp (-(Complex.I * (v : ℂ)))))
      (Set.Ici A) := continuousOn_const.mul (contOn_cpow_mul_expNegI c hA)
  exact (h1.mono (by intro x hx; rw [Set.uIcc_of_le hAB] at hx; exact hx.1)).intervalIntegrable

lemma contOn_Gp (t : ℝ) {A : ℝ} (hA : 0 < A) : ContinuousOn (Gp (ct t)) (Set.Ici A) := by
  refine ContinuousOn.congr (contOn_cpow_mul_expI (ct t) hA) ?_
  intro x hx
  exact Gp_eq_cpow (ct t) (lt_of_lt_of_le hA hx)

lemma contOn_Gm (t : ℝ) {A : ℝ} (hA : 0 < A) : ContinuousOn (Gm (ct t)) (Set.Ici A) := by
  refine ContinuousOn.congr (contOn_cpow_mul_expNegI (ct t) hA) ?_
  intro x hx
  exact Gm_eq_cpow (ct t) (lt_of_lt_of_le hA hx)

lemma contOn_Gp_mul (t : ℝ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun x : ℝ => Gp (ct t) x * (ct t * (x : ℂ)⁻¹ + Complex.I)) (Set.Ici A) := by
  refine (contOn_Gp t hA).mul ?_
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hA hx))
  exact ((continuousAt_const.mul ((continuousAt_inv₀ hx0).comp
    Complex.continuous_ofReal.continuousAt)).add continuousAt_const).continuousWithinAt

lemma contOn_Gm_mul (t : ℝ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun x : ℝ => Gm (ct t) x * (ct t * (x : ℂ)⁻¹ - Complex.I)) (Set.Ici A) := by
  refine (contOn_Gm t hA).mul ?_
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hA hx))
  exact ((continuousAt_const.mul ((continuousAt_inv₀ hx0).comp
    Complex.continuous_ofReal.continuousAt)).sub continuousAt_const).continuousWithinAt

/-! ### Integration by parts on a finite interval -/

lemma ibp_plus (t : ℝ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ))
      = (Gp (ct t) B - Gp (ct t) A
          - Complex.I * ∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))
        / (ct t) := by
  have hct : ct t ≠ 0 := ct_ne_zero t
  have hderivG : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (Gp (ct t)) (Gp (ct t) x * (ct t * (x : ℂ)⁻¹ + Complex.I)) x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact hasDerivAt_Gp (ct t) (ne_of_gt (lt_of_lt_of_le hA hx.1))
  have hintG : IntervalIntegrable
      (fun x : ℝ => Gp (ct t) x * (ct t * (x : ℂ)⁻¹ + Complex.I)) volume A B :=
    ((contOn_Gp_mul t hA).mono
      (by intro x hx; rw [Set.uIcc_of_le hAB] at hx; exact hx.1)).intervalIntegrable
  have hFTC : ∫ x in A..B, Gp (ct t) x * (ct t * (x : ℂ)⁻¹ + Complex.I)
      = Gp (ct t) B - Gp (ct t) A :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivG hintG
  have hpint : IntervalIntegrable
      (fun x : ℝ => ct t * ((x : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (x : ℂ))))
      volume A B := intervalIntegrable_cpow_mul_expI (ct t - 1) (ct t) hA hAB
  have hgint : IntervalIntegrable
      (fun x : ℝ => Complex.I * ((x : ℂ) ^ (ct t) * Complex.exp (Complex.I * (x : ℂ))))
      volume A B := intervalIntegrable_cpow_mul_expI (ct t) Complex.I hA hAB
  have hkey : ct t * (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
      + Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))
      = Gp (ct t) B - Gp (ct t) A := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add hpint hgint, ← hFTC]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hA hx.1
    show ct t * ((x : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (x : ℂ)))
        + Complex.I * ((x : ℂ) ^ (ct t) * Complex.exp (Complex.I * (x : ℂ)))
      = Gp (ct t) x * (ct t * (x : ℂ)⁻¹ + Complex.I)
    rw [Gp_eq_cpow (ct t) hx0]
    exact (Gp_mul_eq t hx0).symm
  rw [eq_div_iff hct]
  linear_combination hkey

lemma ibp_minus (t : ℝ) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ)))
      = (Gm (ct t) B - Gm (ct t) A
          + Complex.I * ∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))
        / (ct t) := by
  have hct : ct t ≠ 0 := ct_ne_zero t
  have hderivG : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (Gm (ct t)) (Gm (ct t) x * (ct t * (x : ℂ)⁻¹ - Complex.I)) x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact hasDerivAt_Gm (ct t) (ne_of_gt (lt_of_lt_of_le hA hx.1))
  have hintG : IntervalIntegrable
      (fun x : ℝ => Gm (ct t) x * (ct t * (x : ℂ)⁻¹ - Complex.I)) volume A B :=
    ((contOn_Gm_mul t hA).mono
      (by intro x hx; rw [Set.uIcc_of_le hAB] at hx; exact hx.1)).intervalIntegrable
  have hFTC : ∫ x in A..B, Gm (ct t) x * (ct t * (x : ℂ)⁻¹ - Complex.I)
      = Gm (ct t) B - Gm (ct t) A :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivG hintG
  have hpint : IntervalIntegrable
      (fun x : ℝ => ct t * ((x : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (x : ℂ)))))
      volume A B := intervalIntegrable_cpow_mul_expNegI (ct t - 1) (ct t) hA hAB
  have hgint : IntervalIntegrable
      (fun x : ℝ => Complex.I * ((x : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (x : ℂ)))))
      volume A B := intervalIntegrable_cpow_mul_expNegI (ct t) Complex.I hA hAB
  have hkey : ct t * (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))
      - Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))
      = Gm (ct t) B - Gm (ct t) A := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hpint hgint, ← hFTC]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hA hx.1
    show ct t * ((x : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (x : ℂ))))
        - Complex.I * ((x : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (x : ℂ))))
      = Gm (ct t) x * (ct t * (x : ℂ)⁻¹ - Complex.I)
    rw [Gm_eq_cpow (ct t) hx0]
    exact (Gm_mul_eq t hx0).symm
  rw [eq_div_iff hct]
  linear_combination hkey

/-! ### The core bound on a finite interval -/

lemma sinTailCore (t : ℝ) (ht : 4 ≤ t) {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) {C₁ : ℝ}
    (hC₁ : 0 < C₁)
    (hJp : ‖∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ))‖ ≤ C₁)
    (hJm : ‖∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ)))‖ ≤ 4) :
    ‖∫ v in A..B, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1)‖ ≤ (8 + C₁) / (2 * t) := by
  have ht0 : 0 < t := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB0 : 0 < B := lt_of_lt_of_le hA0 hAB
  have hct : ct t ≠ 0 := ct_ne_zero t
  have hctle : t ≤ ‖ct t‖ := le_norm_ct ht0.le
  have hpint : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (x : ℂ))) volume A B :=
    ((contOn_cpow_mul_expI (ct t - 1) hA0).mono
      (by intro x hx; rw [Set.uIcc_of_le hAB] at hx; exact hx.1)).intervalIntegrable
  have hmint : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (x : ℂ)))) volume A B :=
    ((contOn_cpow_mul_expNegI (ct t - 1) hA0).mono
      (by intro x hx; rw [Set.uIcc_of_le hAB] at hx; exact hx.1)).intervalIntegrable
  have hsplit : ∫ v in A..B, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1)
      = (1 / (2 * Complex.I)) *
          ((∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
            - (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))) := by
    have hpt : ∀ x ∈ Set.uIcc A B, ((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ (ct t - 1)
        = (1 / (2 * Complex.I)) * ((x : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (x : ℂ)))
          - (1 / (2 * Complex.I)) * ((x : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (x : ℂ)))) := by
      intro x hx
      rw [sin_mul_cpow_split]
      ring
    calc ∫ v in A..B, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1)
        = ∫ v in A..B, ((1 / (2 * Complex.I)) *
              ((v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
            - (1 / (2 * Complex.I)) *
              ((v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))) :=
          intervalIntegral.integral_congr hpt
      _ = (∫ v in A..B, (1 / (2 * Complex.I)) *
              ((v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ))))
            - (∫ v in A..B, (1 / (2 * Complex.I)) *
              ((v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))) :=
          intervalIntegral.integral_sub (hpint.const_mul _) (hmint.const_mul _)
      _ = (1 / (2 * Complex.I)) * (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
            - (1 / (2 * Complex.I)) * (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ)))) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = (1 / (2 * Complex.I)) *
          ((∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
            - (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))) := by
          ring
  have hp : ‖∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ))‖
      ≤ (2 + C₁) / t := by
    rw [ibp_plus t hA0 hAB, norm_div]
    have hnum : ‖Gp (ct t) B - Gp (ct t) A
        - Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))‖
        ≤ 2 + C₁ := by
      have hb : ‖Gp (ct t) B‖ ≤ 1 := by
        rw [norm_Gp_ct t hB0]
        exact Real.rpow_le_one_of_one_le_of_nonpos (le_trans hA hAB) (by norm_num)
      have ha : ‖Gp (ct t) A‖ ≤ 1 := by
        rw [norm_Gp_ct t hA0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
      have hI : ‖Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))‖
          ≤ C₁ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact hJp
      calc ‖Gp (ct t) B - Gp (ct t) A
            - Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))‖
          ≤ ‖Gp (ct t) B - Gp (ct t) A‖
            + ‖Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))‖ :=
              norm_sub_le _ _
        _ ≤ (‖Gp (ct t) B‖ + ‖Gp (ct t) A‖)
            + ‖Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))‖ := by
              gcongr
              exact norm_sub_le _ _
        _ ≤ (1 + 1) + C₁ := by linarith
        _ = 2 + C₁ := by ring
    calc ‖Gp (ct t) B - Gp (ct t) A
          - Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ)))‖ / ‖ct t‖
        ≤ (2 + C₁) / ‖ct t‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (2 + C₁) / t := div_le_div_of_nonneg_left (by linarith) ht0 hctle
  have hm : ‖∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ)))‖
      ≤ 6 / t := by
    rw [ibp_minus t hA0 hAB, norm_div]
    have hnum : ‖Gm (ct t) B - Gm (ct t) A
        + Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))‖
        ≤ 6 := by
      have hb : ‖Gm (ct t) B‖ ≤ 1 := by
        rw [norm_Gm_ct t hB0]
        exact Real.rpow_le_one_of_one_le_of_nonpos (le_trans hA hAB) (by norm_num)
      have ha : ‖Gm (ct t) A‖ ≤ 1 := by
        rw [norm_Gm_ct t hA0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
      have hI : ‖Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))‖
          ≤ 4 := by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact hJm
      calc ‖Gm (ct t) B - Gm (ct t) A
            + Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))‖
          ≤ ‖Gm (ct t) B - Gm (ct t) A‖
            + ‖Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))‖ :=
              norm_add_le _ _
        _ ≤ (‖Gm (ct t) B‖ + ‖Gm (ct t) A‖)
            + ‖Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))‖ := by
              gcongr
              exact norm_sub_le _ _
        _ ≤ (1 + 1) + 4 := by linarith
        _ = 6 := by ring
    calc ‖Gm (ct t) B - Gm (ct t) A
          + Complex.I * (∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ))))‖ / ‖ct t‖
        ≤ 6 / ‖ct t‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ 6 / t := div_le_div_of_nonneg_left (by norm_num) ht0 hctle
  have hnorm2I : ‖((1 / (2 * Complex.I)) : ℂ)‖ = 1 / 2 := by
    have hI2 : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
    have h2 : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
      field_simp
      rw [hI2]
      ring
    rw [h2, norm_neg, norm_div, Complex.norm_I]
    norm_num
  rw [hsplit, norm_mul, hnorm2I]
  have hsub : ‖(∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
      - (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))‖
      ≤ (2 + C₁) / t + 6 / t := by
    refine (norm_sub_le _ _).trans ?_
    linarith [hp, hm]
  calc (1 / 2) * ‖(∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (Complex.I * (v : ℂ)))
        - (∫ v in A..B, (v : ℂ) ^ (ct t - 1) * Complex.exp (-(Complex.I * (v : ℂ))))‖
      ≤ (1 / 2) * ((2 + C₁) / t + 6 / t) := by
        exact mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ = (8 + C₁) / (2 * t) := by ring

/-! ### Passing to the half-line -/

lemma integrableOn_sinTail {t A : ℝ} (hA : 1 ≤ A) :
    MeasureTheory.IntegrableOn
      (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1)) (Set.Ioi A) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hgi : Integrable (fun v : ℝ => v ^ (-(3/2) : ℝ)) (volume.restrict (Set.Ioi A)) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3/2 : ℝ)) (by norm_num) hA0
  have hcont : ContinuousOn (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1))
      (Set.Ioi A) :=
    (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sin.continuousOn).mul
      ((contOn_cpow (ct t - 1) hA0).mono (by
        intro x hx
        exact Set.mem_Ici.mpr (le_of_lt hx)))
  refine hgi.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
  have hv0 : 0 < v := lt_trans hA0 hv
  rw [norm_mul, norm_ofReal_complex, Complex.norm_cpow_eq_rpow_re_of_pos hv0, ct_sub_one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv0.le _) (Real.abs_sin_le_one v)

lemma sinTailIoi (t : ℝ) (ht : 4 ≤ t) {A : ℝ} (hA : 1 ≤ A) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hJp : ∀ B : ℝ, A ≤ B →
      ‖∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (Complex.I * (v : ℂ))‖ ≤ C₁)
    (hJm : ∀ B : ℝ, A ≤ B →
      ‖∫ v in A..B, (v : ℂ) ^ (ct t) * Complex.exp (-(Complex.I * (v : ℂ)))‖ ≤ 4) :
    ‖∫ v in Set.Ioi A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1)‖ ≤ (8 + C₁) / (2 * t) := by
  refine Work.ZeroDensity.Ingham.AfeSelf.ioiIntervalBoundAux (f := fun v : ℝ =>
    ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (ct t - 1)) (integrableOn_sinTail (t := t) hA) ?_
  intro B hB
  exact sinTailCore t ht hA hB hC₁ (hJp B hB) (hJm B hB)

end

end Work.ZeroDensity.Zeta.SinAux
