import Mathlib
import Submission.Work.FIArea4.logSine_defs
import Submission.Work.FIArea4.logSine_tau_bound
import Submission.Work.FIArea4.logSine_harmonic_bound
import Submission.Work.FIArea4.logSine_tail_sq_bound
import Submission.Work.FIArea4.logSine_psi_deriv
import Submission.Work.FIArea4.logSine_integral_deriv
import Submission.Work.FIArea4.logSine_integral_deriv2

namespace Work.FIArea4

open scoped BigOperators Topology ContDiff
open Filter MeasureTheory
open intervalIntegral

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma logSine_natCast_le_infty (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by
  show ((n : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  rw [WithTop.coe_le_coe]; exact le_top

lemma logSine_hN1_of {N : ℕ} (hN : 2 ≤ N) : 1 ≤ N := le_trans (by norm_num) hN

lemma logSine_ufunC_periodic (N : ℕ) (α : ℝ) : ufunC N (α + 2 * Real.pi) = ufunC N α := by
  simp only [ufunC, ufun_periodic]

lemma logSine_continuous_ufunC (N : ℕ) (hN : 1 ≤ N) : Continuous (ufunC N) :=
  Complex.continuous_ofReal.comp (contDiff_ufun N hN).continuous

/-- `ufun N` as a continuous `2π`-periodic complex valued function. -/
def logSine_Ffun (N : ℕ) (hN : 1 ≤ N) : C(AddCircle (2 * Real.pi), ℂ) :=
  { toFun := AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (ufunC N)
    continuous_toFun := by
      apply AddCircle.liftIoc_continuous
      · rw [← logSine_ufunC_periodic N (-Real.pi)]
      · exact (logSine_continuous_ufunC N hN).continuousOn }

lemma logSine_Ffun_coe (N : ℕ) (hN : 1 ≤ N) :
    ⇑(logSine_Ffun N hN) = AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (ufunC N) := rfl

lemma logSine_hab_pi : -Real.pi < Real.pi := by linarith [Real.pi_pos]

lemma logSine_Ffun_coe_eq (N : ℕ) (hN : 1 ≤ N) {α : ℝ} (hα : α ∈ Set.Ioc (-Real.pi) Real.pi) :
    logSine_Ffun N hN (α : AddCircle (2 * Real.pi)) = ufunC N α := by
  rw [logSine_Ffun_coe]
  refine AddCircle.liftIoc_coe_apply ?_
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  exact hα

lemma logSine_ufunC_pi_eq_neg (N : ℕ) : ufunC N Real.pi = ufunC N (-Real.pi) := by
  have h := logSine_ufunC_periodic N (-Real.pi)
  rwa [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h

/-- `fourierCoeffOn` only depends on the interval through its endpoints. -/
lemma logSine_fourierCoeffOn_eq_of_eq {a b₁ b₂ : ℝ} {f : ℝ → ℂ} {n : ℤ} (h : b₁ = b₂)
    (hab₁ : a < b₁) (hab₂ : a < b₂) :
    fourierCoeffOn hab₁ f n = fourierCoeffOn hab₂ f n := by
  subst h
  exact congrArg (fun hh => fourierCoeffOn hh f n) (Subsingleton.elim hab₁ hab₂)

lemma logSine_fourierCoeff_Ffun_eq (N : ℕ) (hN : 1 ≤ N) (ℓ : ℤ) :
    fourierCoeff (⇑(logSine_Ffun N hN)) ℓ = fourierCoeffOn logSine_hab_pi (ufunC N) ℓ := by
  have h1 : fourierCoeff (AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (ufunC N)) ℓ
      = fourierCoeffOn (lt_add_of_pos_right (-Real.pi) (Fact.out : 0 < 2 * Real.pi))
          (ufunC N) ℓ := fourierCoeff_liftIoc_eq _ _
  rw [show fourierCoeff (⇑(logSine_Ffun N hN)) ℓ
      = fourierCoeff (AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (ufunC N)) ℓ from rfl, h1]
  exact logSine_fourierCoeffOn_eq_of_eq (by ring : -Real.pi + 2 * Real.pi = Real.pi) _ _

/-! ### Derivatives of `ufun` -/

/-- First complex derivative data for `ufun N`. -/
def logSine_dufunC (N : ℕ) : ℝ → ℂ := fun x => ((deriv (ufun N)) x : ℂ)

/-- Second complex derivative data for `ufun N`. -/
def logSine_d2ufunC (N : ℕ) : ℝ → ℂ := fun x => ((deriv (deriv (ufun N))) x : ℂ)

lemma logSine_hasDerivAt_ufunC (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    HasDerivAt (fun y => ufunC N y) (logSine_dufunC N x) x := by
  have h1 : ContDiff ℝ 1 (ufun N) := (contDiff_ufun N hN).of_le (logSine_natCast_le_infty 1)
  have hd : HasDerivAt (ufun N) (deriv (ufun N) x) x :=
    (h1.differentiable (by norm_num) x).hasDerivAt
  simpa [logSine_dufunC, ufunC] using hd.ofReal_comp

lemma logSine_contDiff_deriv_ufun1 (N : ℕ) (hN : 1 ≤ N) : ContDiff ℝ 1 (deriv (ufun N)) :=
  (contDiff_succ_iff_deriv.mp ((contDiff_ufun N hN).of_le (logSine_natCast_le_infty 2))).2.2

lemma logSine_contDiff_deriv_ufun2 (N : ℕ) (hN : 1 ≤ N) :
    ContDiff ℝ 1 (deriv (deriv (ufun N))) := by
  have h2 : ContDiff ℝ 2 (deriv (ufun N)) :=
    (contDiff_succ_iff_deriv.mp ((contDiff_ufun N hN).of_le (logSine_natCast_le_infty 3))).2.2
  exact (contDiff_succ_iff_deriv.mp h2).2.2

lemma logSine_hasDerivAt_dufunC (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    HasDerivAt (fun y => logSine_dufunC N y) (logSine_d2ufunC N x) x := by
  have hd : HasDerivAt (deriv (ufun N)) (deriv (deriv (ufun N)) x) x :=
    ((logSine_contDiff_deriv_ufun1 N hN).differentiable (by norm_num) x).hasDerivAt
  simpa [logSine_dufunC, logSine_d2ufunC] using hd.ofReal_comp

lemma logSine_deriv_periodic {f : ℝ → ℝ} (hd : Differentiable ℝ f) {c : ℝ}
    (hf : ∀ y, f (y + c) = f y) (x : ℝ) : deriv f (x + c) = deriv f x := by
  have hfun : (fun y : ℝ => f (y + c)) = f := funext hf
  have h1 : deriv (fun y : ℝ => f (y + c)) x = deriv f x := by rw [hfun]
  have h2 : deriv (fun y : ℝ => f (y + c)) x = deriv f (x + c) := by
    rw [show (fun y : ℝ => f (y + c)) = f ∘ (fun y : ℝ => y + c) from rfl]
    rw [deriv_comp x (hd (x + c)) (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y + c) x)]
    simp
  rw [← h2, h1]

lemma logSine_differentiable_ufun (N : ℕ) (hN : 1 ≤ N) : Differentiable ℝ (ufun N) :=
  ((contDiff_ufun N hN).of_le (logSine_natCast_le_infty 1)).differentiable (by norm_num)

lemma logSine_dufunC_periodic (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    logSine_dufunC N (x + 2 * Real.pi) = logSine_dufunC N x := by
  have hf : ∀ y : ℝ, ufun N (y + 2 * Real.pi) = ufun N y := fun y => ufun_periodic N y
  simp only [logSine_dufunC]
  rw [logSine_deriv_periodic (logSine_differentiable_ufun N hN) hf]

lemma logSine_intervalIntegrable_dufunC (N : ℕ) (hN : 1 ≤ N) :
    IntervalIntegrable (logSine_dufunC N) volume (-Real.pi) Real.pi :=
  (Complex.continuous_ofReal.comp (logSine_contDiff_deriv_ufun1 N hN).continuous).intervalIntegrable _ _

lemma logSine_intervalIntegrable_d2ufunC (N : ℕ) (hN : 1 ≤ N) :
    IntervalIntegrable (logSine_d2ufunC N) volume (-Real.pi) Real.pi :=
  (Complex.continuous_ofReal.comp (logSine_contDiff_deriv_ufun2 N hN).continuous).intervalIntegrable _ _

/-! ### Integration by parts -/

lemma logSine_fourierCoeffOn_ufunC_eq (N : ℕ) (hN : 1 ≤ N) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    fourierCoeffOn logSine_hab_pi (ufunC N) ℓ
      = fourierCoeffOn logSine_hab_pi (logSine_dufunC N) ℓ / (Complex.I * (ℓ : ℂ)) := by
  have h := fourierCoeffOn_of_hasDerivAt logSine_hab_pi hℓ
    (f := ufunC N) (f' := logSine_dufunC N) (fun x _ => logSine_hasDerivAt_ufunC N hN x)
    (logSine_intervalIntegrable_dufunC N hN)
  have hb : ufunC N Real.pi - ufunC N (-Real.pi) = 0 := by
    rw [logSine_ufunC_pi_eq_neg N, sub_self]
  rw [h, hb, mul_zero, zero_sub]
  have hpi : (↑Real.pi : ℂ) - ↑(-Real.pi) = 2 * ↑Real.pi := by push_cast; ring
  rw [hpi]
  have hI : Complex.I * (ℓ : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Int.cast_ne_zero.mpr hℓ]
  rw [eq_div_iff hI]
  field_simp

lemma logSine_fourierCoeffOn_dufunC_eq (N : ℕ) (hN : 1 ≤ N) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    fourierCoeffOn logSine_hab_pi (logSine_dufunC N) ℓ
      = fourierCoeffOn logSine_hab_pi (logSine_d2ufunC N) ℓ / (Complex.I * (ℓ : ℂ)) := by
  have h := fourierCoeffOn_of_hasDerivAt logSine_hab_pi hℓ
    (f := logSine_dufunC N) (f' := logSine_d2ufunC N) (fun x _ => logSine_hasDerivAt_dufunC N hN x)
    (logSine_intervalIntegrable_d2ufunC N hN)
  have hb : logSine_dufunC N Real.pi - logSine_dufunC N (-Real.pi) = 0 := by
    have hp := logSine_dufunC_periodic N hN (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hp
    rw [hp, sub_self]
  rw [h, hb, mul_zero, zero_sub]
  have hpi : (↑Real.pi : ℂ) - ↑(-Real.pi) = 2 * ↑Real.pi := by push_cast; ring
  rw [hpi]
  have hI : Complex.I * (ℓ : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Int.cast_ne_zero.mpr hℓ]
  rw [eq_div_iff hI]
  field_simp

/-! ### Elementary complex norm facts -/

lemma logSine_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r]

/-! ### The sup-norm bound for `ufun` -/

lemma logSine_abs_Psi_le_log (N : ℕ) (hN : 2 ≤ N) {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    |Psi N y| ≤ Real.log N := by
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  rcases le_or_gt (2 * (N : ℝ) ^ 2 * y - 1) 0 with h | h
  · rw [Psi_eq_zero h, abs_zero]; exact hNlog
  · have hypos : 0 < y := by
      nlinarith [h, hy0, sq_nonneg (N : ℝ)]
    have hlog : |Real.log (2 * y)| ≤ 2 * Real.log N := by
      rw [abs_le]
      constructor
      · have h1 : (1 : ℝ) / (N : ℝ) ^ 2 ≤ 2 * y := by
          have hN2 : (0:ℝ) < (N:ℝ)^2 := by positivity
          have : 1 < 2 * (N:ℝ)^2 * y := by linarith
          rw [div_le_iff₀ hN2]
          nlinarith [this, hN2]
        have h2 := Real.log_le_log (by positivity : (0:ℝ) < 1 / (N:ℝ)^2) h1
        have h3 : Real.log (1 / (N : ℝ) ^ 2) = -2 * Real.log N := by
          rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, Real.log_one]
          ring
        linarith
      · have h1 : 2 * y ≤ 4 := by linarith
        have h2 := Real.log_le_log (by positivity : (0:ℝ) < 2 * y) h1
        have h3 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
        have h4 : Real.log 2 ≤ Real.log N :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hN)
        linarith
    have hτ0 : 0 ≤ Real.smoothTransition (2 * (N:ℝ)^2 * y - 1) := Real.smoothTransition.nonneg _
    have hτ1 : Real.smoothTransition (2 * (N:ℝ)^2 * y - 1) ≤ 1 := Real.smoothTransition.le_one _
    rw [Psi, abs_mul, abs_mul, abs_of_nonneg hτ0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have h1 : (1/2 : ℝ) * Real.smoothTransition (2 * (N:ℝ)^2 * y - 1) * |Real.log (2 * y)|
        ≤ (1/2 : ℝ) * 1 * (2 * Real.log N) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hτ1 (by norm_num)
      · exact hlog
      · exact abs_nonneg _
      · norm_num
    linarith

lemma logSine_abs_ufun_le (N : ℕ) (hN : 2 ≤ N) (α : ℝ) : |ufun N α| ≤ 4 * Real.log N := by
  have hg0 : 0 ≤ 1 - Real.cos α := by linarith [Real.cos_le_one α]
  have hg2 : 1 - Real.cos α ≤ 2 := by linarith [Real.neg_one_le_cos α]
  have hh0 : 0 ≤ 1 + Real.cos α := by linarith [Real.neg_one_le_cos α]
  have hh2 : 1 + Real.cos α ≤ 2 := by linarith [Real.cos_le_one α]
  have h1 : |Psi N (1 - Real.cos α)| ≤ Real.log N := logSine_abs_Psi_le_log N hN hg0 hg2
  have h2 : |Psi N (1 + Real.cos α)| ≤ Real.log N := logSine_abs_Psi_le_log N hN hh0 hh2
  have h3 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have h4 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have h5 : |2 * Real.log 2| = 2 * Real.log 2 := by
    rw [abs_of_nonneg (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)])]
  rw [ufun]
  have h6 : |(-Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α)) + 2 * Real.log 2|
      ≤ (|Psi N (1 - Real.cos α)| + |Psi N (1 + Real.cos α)|) + 2 * Real.log 2 := by
    have h7 : |(-Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α)) + 2 * Real.log 2|
        ≤ |(-Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α))| + |2 * Real.log 2| :=
      abs_add_le _ _
    rw [h5] at h7
    have h8 : |(-Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α))|
        ≤ |Psi N (1 - Real.cos α)| + |Psi N (1 + Real.cos α)| := by
      have h9 : (-Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α))
          = (-Psi N (1 - Real.cos α)) + (-Psi N (1 + Real.cos α)) := by ring
      rw [h9]
      calc |(-Psi N (1 - Real.cos α)) + (-Psi N (1 + Real.cos α))|
          ≤ |(-Psi N (1 - Real.cos α))| + |(-Psi N (1 + Real.cos α))| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_neg]
    linarith
  linarith

/-! ### Bounds on the Fourier coefficients -/

/-- The norm of an interval Fourier coefficient is at most `(2π)⁻¹ ∫ ‖f‖`. -/
lemma logSine_norm_fourierCoeffOn_le (f : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn logSine_hab_pi f n‖ ≤ (1/(2*Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ := by
  rw [fourierCoeffOn_eq_integral _ _ logSine_hab_pi, norm_smul]
  rw [show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
  have hsc : ‖(1 / (2*Real.pi) : ℝ)‖ = 1/(2*Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hsc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∫ x in (-Real.pi)..Real.pi, fourier (-n) (x : AddCircle (2 * Real.pi)) • f x‖
      ≤ ∫ x in (-Real.pi)..Real.pi,
          ‖fourier (-n) (x : AddCircle (2 * Real.pi)) • f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm logSine_hab_pi.le
    _ = ∫ x in (-Real.pi)..Real.pi, ‖f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        show ‖fourier (-n) (x : AddCircle (2 * Real.pi)) • f x‖ = ‖f x‖
        rw [smul_eq_mul, norm_mul,
          show ‖fourier (-n) (x : AddCircle (2 * Real.pi))‖ = (1:ℝ) by
            rw [fourier_apply, Circle.norm_coe],
          one_mul]

lemma logSine_norm_fourierCoeffOn_dufunC_le (N : ℕ) (hN : 1 ≤ N) (ℓ : ℤ) :
    ‖fourierCoeffOn logSine_hab_pi (logSine_dufunC N) ℓ‖
      ≤ (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α| := by
  refine le_trans (logSine_norm_fourierCoeffOn_le (logSine_dufunC N) ℓ) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro x _
  simp only [logSine_dufunC, logSine_norm_ofReal]

lemma logSine_norm_fourierCoeffOn_d2ufunC_le (N : ℕ) (hN : 1 ≤ N) (ℓ : ℤ) :
    ‖fourierCoeffOn logSine_hab_pi (logSine_d2ufunC N) ℓ‖
      ≤ (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α| := by
  refine le_trans (logSine_norm_fourierCoeffOn_le (logSine_d2ufunC N) ℓ) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro x _
  simp only [logSine_d2ufunC, logSine_norm_ofReal]

lemma logSine_norm_fourierCoeffOn_ufunC_zero_le (N : ℕ) (hN : 2 ≤ N) :
    ‖fourierCoeffOn logSine_hab_pi (ufunC N) 0‖ ≤ 4 * Real.log N := by
  refine le_trans (logSine_norm_fourierCoeffOn_le (ufunC N) 0) ?_
  have hzero : (∫ x in (-Real.pi)..Real.pi, ‖ufunC N x‖)
      ≤ (4 * Real.log N) * (Real.pi - (-Real.pi)) := by
    have h1 := intervalIntegral.integral_mono_on (μ := volume) logSine_hab_pi.le
      ((logSine_continuous_ufunC N (logSine_hN1_of hN)).norm.intervalIntegrable _ _) intervalIntegrable_const
      (fun x _ => by simp only [ufunC, logSine_norm_ofReal]; exact logSine_abs_ufun_le N hN x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h1
    exact h1
  calc (1/(2*Real.pi)) * (∫ x in (-Real.pi)..Real.pi, ‖ufunC N x‖)
      ≤ (1/(2*Real.pi)) * ((4 * Real.log N) * (Real.pi - (-Real.pi))) :=
        mul_le_mul_of_nonneg_left hzero (by positivity)
    _ = 4 * Real.log N := by
        rw [show Real.pi - (-Real.pi) = 2 * Real.pi by ring]
        field_simp

/-! ### Summability of the tail -/

lemma logSine_summable_int_inv_sq (B : ℝ) : Summable (fun ℓ : ℤ => B / ((ℓ:ℝ)^2)) := by
  have hnat : Summable (fun n : ℕ => B / ((n:ℝ)^2)) := by
    have h : Summable (fun n : ℕ => (1:ℝ) / ((n:ℝ)^2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (h.mul_left B).congr (fun n => by rw [mul_one_div])
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨hnat, ?_⟩
  exact hnat.congr (fun n => by push_cast; ring)

lemma logSine_summable_int_tail (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    Summable (fun ℓ : ℤ => if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0) := by
  refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) (logSine_summable_int_inv_sq B)
  · split
    · exact div_nonneg hB (by positivity)
    · exact le_refl 0
  · split
    · exact le_refl _
    · exact div_nonneg hB (by positivity)

/-! ### Pointwise bounds for the Fourier coefficients of `logSine_Ffun` -/

lemma logSine_norm_Ffun_coeff_le_harm (N : ℕ) (hN : 2 ≤ N) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ‖fourierCoeff (⇑(logSine_Ffun N (logSine_hN1_of hN))) ℓ‖
      ≤ ((1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α|)
          / |(ℓ:ℝ)| := by
  rw [logSine_fourierCoeff_Ffun_eq, logSine_fourierCoeffOn_ufunC_eq N (logSine_hN1_of hN) hℓ, norm_div]
  rw [show ‖Complex.I * (ℓ:ℂ)‖ = |(ℓ:ℝ)| by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]]
  exact div_le_div_of_nonneg_right (logSine_norm_fourierCoeffOn_dufunC_le N (logSine_hN1_of hN) ℓ) (abs_nonneg _)

lemma logSine_norm_Ffun_coeff_le_sq (N : ℕ) (hN : 2 ≤ N) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ‖fourierCoeff (⇑(logSine_Ffun N (logSine_hN1_of hN))) ℓ‖
      ≤ ((1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α|)
          / ((ℓ:ℝ)^2) := by
  rw [logSine_fourierCoeff_Ffun_eq, logSine_fourierCoeffOn_ufunC_eq N (logSine_hN1_of hN) hℓ,
    logSine_fourierCoeffOn_dufunC_eq N (logSine_hN1_of hN) hℓ, div_div, norm_div]
  rw [show ‖Complex.I * (ℓ:ℂ) * (Complex.I * (ℓ:ℂ))‖ = (ℓ:ℝ)^2 by
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    rw [← sq, sq_abs]]
  exact div_le_div_of_nonneg_right (logSine_norm_fourierCoeffOn_d2ufunC_le N (logSine_hN1_of hN) ℓ) (by positivity)

lemma logSine_norm_Ffun_coeff_zero_le (N : ℕ) (hN : 2 ≤ N) :
    ‖fourierCoeff (⇑(logSine_Ffun N (logSine_hN1_of hN))) 0‖ ≤ 4 * Real.log N := by
  rw [logSine_fourierCoeff_Ffun_eq]
  exact logSine_norm_fourierCoeffOn_ufunC_zero_le N hN

lemma logSine_zero_mem_Icc (N : ℕ) : (0:ℤ) ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
  rw [Finset.mem_Icc]
  constructor <;> omega

/-- **The mollified log-sine Fourier expansion (15.5)–(15.7).**  There is an **absolute**
constant `C` such that for every `N ≥ 2` there is a family `c : ℤ → ℂ` with
`Σ_ℓ ‖c ℓ‖ ≤ C (log N)²` and

  `-log(1/2 |sin α|) = Re Σ_ℓ c ℓ e^{iℓα}`   for `2/N ≤ |α| ≤ 1`.

(At `α = α₂ - α₁` for a pair `z₁, z₂` of *FI* (5.14) with `|z₁|,|z₂| ≍ √N` and `|Δ| ≥ 4dX ≥ 4`,
the left-hand side is exactly the logarithmic factor `log(2|z₁z₂|/|Δ|)` of (7.2)/(15.4), and
`|α| ≥ 2/N` because `|Δ| = |z₁z₂||sin α|`; also `|α| < 2πθ ≤ 1` since the box has angle `2πθ`.)

The coefficients may be those of **any** mollified version `u(α) = -h(N·d(α))·log(1/2|sin α|)`
with `d(α)=dist(α,2πℤ)`, `h` smooth, `h(β) = 0` for `|β| ≤ 1`, `h(β) = 1` for `|β| ≥ 2`,
`|h| ≤ 1`; it suffices to prove the stated consequences for such a `u` (this `u` is `C^∞` and
`2π`-periodic, and equals `-log(1/2|sin α|)` on the stated range).  Its Fourier series converges
absolutely, hence uniformly, so the identity holds at every point of that range; the `(log N)²`
is the balance between `Σ_{1≤ℓ≤N}(log N)/ℓ` and the rapid decay beyond `ℓ > N`. -/
theorem logSine_fourier :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∃ c : ℤ → ℂ,
      (∑' l : ℤ, ‖c l‖) ≤ C * (Real.log N) ^ (2 : ℕ) ∧
      (∀ α : ℝ, 2 / (N : ℝ) ≤ |α| → |α| ≤ 1 →
        -Real.log (|Real.sin α| / 2)
          = (∑' l : ℤ, c l * Complex.exp (Complex.I * (l : ℂ) * (α : ℂ))).re) := by
  classical
  obtain ⟨Ci1, hCi1pos, hCi1⟩ := logSine_integral_deriv
  obtain ⟨Ci2, hCi2pos, hCi2⟩ := logSine_integral_deriv2
  obtain ⟨Ch3, hCh3pos, hCh3⟩ := logSine_harmonic_bound
  obtain ⟨Ct4, hCt4pos, hCt4⟩ := logSine_tail_sq_bound
  refine ⟨Ci1 * Ch3 / (2 * Real.pi) + Ci2 * Ct4 / (2 * Real.pi * Real.log 2)
      + 4 / Real.log 2 + 1, by positivity, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := logSine_hN1_of hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  set A : ℝ := (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α| with hAdef
  set B : ℝ := (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α| with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg logSine_hab_pi.le (fun x _ => abs_nonneg _))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg logSine_hab_pi.le (fun x _ => abs_nonneg _))
  have hAb : A ≤ Ci1 * Real.log N / (2*Real.pi) := by
    rw [hAdef]
    calc (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α|
        ≤ (1/(2*Real.pi)) * (Ci1 * Real.log N) :=
          mul_le_mul_of_nonneg_left (hCi1 N hN) (by positivity)
      _ = Ci1 * Real.log N / (2*Real.pi) := by ring
  have hBb : B ≤ Ci2 * (N:ℝ) * Real.log N / (2*Real.pi) := by
    rw [hBdef]
    calc (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α|
        ≤ (1/(2*Real.pi)) * (Ci2 * (N:ℝ) * Real.log N) :=
          mul_le_mul_of_nonneg_left (hCi2 N hN) (by positivity)
      _ = Ci2 * (N:ℝ) * Real.log N / (2*Real.pi) := by ring
  have hpartial : ∀ u : Finset ℤ,
      ∑ ℓ ∈ u, ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
        ≤ 4 * Real.log N + A * (Ch3 * Real.log N) + B * (Ct4 / N) := by
    intro u
    set s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ) with hsdef
    have h0s : (0:ℤ) ∈ s := by rw [hsdef]; exact logSine_zero_mem_Icc N
    rw [← Finset.sum_filter_add_sum_filter_not u (fun ℓ => ℓ ∈ s)
      (fun ℓ => ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖)]
    have h1 : ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
        ≤ 4 * Real.log N + A * (Ch3 * Real.log N) := by
      have h1a : ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
          ≤ ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s),
              (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|) := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        by_cases h0 : ℓ = 0
        · subst h0
          rw [if_pos rfl]
          exact logSine_norm_Ffun_coeff_zero_le N hN
        · rw [if_neg h0, hAdef]
          exact logSine_norm_Ffun_coeff_le_harm N hN h0
      have h1b : ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s),
            (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|)
          ≤ ∑ ℓ ∈ s, (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (s := u.filter (fun ℓ => ℓ ∈ s)) (t := s) ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro ℓ _ _
          by_cases h0 : ℓ = 0
          · rw [if_pos h0]; positivity
          · rw [if_neg h0]; exact div_nonneg hA0 (abs_nonneg _)
      have h1c : ∑ ℓ ∈ s, (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|)
          ≤ 4 * Real.log N + A * (Ch3 * Real.log N) := by
        rw [← Finset.sum_erase_add s
            (fun x => if x = 0 then 4 * Real.log N else A / |(x:ℝ)|) (a := 0) h0s,
          if_pos rfl]
        have hsum1 : ∑ x ∈ s.erase 0, (if x = 0 then 4 * Real.log N else A / |(x:ℝ)|)
            = ∑ x ∈ s.erase 0, A / |(x:ℝ)| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [if_neg (Finset.mem_erase.mp hx).1]
        rw [hsum1]
        have hmul : ∑ x ∈ s.erase 0, A / |(x:ℝ)| = A * ∑ x ∈ s.erase 0, (1 / |(x:ℝ)|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [div_eq_mul_one_div]
        rw [hmul]
        have hbound : ∑ x ∈ s.erase 0, (1:ℝ) / |(x:ℝ)| ≤ Ch3 * Real.log N := by
          rw [hsdef]; exact hCh3 N hN
        have := mul_le_mul_of_nonneg_left hbound hA0
        linarith
      linarith
    have h2 : ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
        ≤ B * (Ct4 / N) := by
      have h2a : ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
          ≤ ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)),
              (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0) := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have hnot : ℓ ∉ s := (Finset.mem_filter.mp hℓ).2
        have hgt : (N:ℤ) < |ℓ| := by
          rw [← not_le]
          intro hle
          exact hnot (by rw [hsdef, Finset.mem_Icc]; exact abs_le.mp hle)
        have hne : ℓ ≠ 0 := by
          intro h0; exact hnot (h0 ▸ h0s)
        rw [if_pos hgt, hBdef]
        exact logSine_norm_Ffun_coeff_le_sq N hN hne
      have h2b : ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)),
            (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0)
          ≤ ∑' ℓ : ℤ, (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0) :=
        Summable.sum_le_tsum _ (fun i _ => by split <;> positivity) (logSine_summable_int_tail B hB0 N)
      have h2c : (∑' ℓ : ℤ, (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0))
          ≤ B * (Ct4 / N) := by
        rw [show (fun ℓ : ℤ => if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0)
            = (fun ℓ : ℤ => B * (if (N:ℤ) < |ℓ| then (1:ℝ) / ((ℓ:ℝ)^2) else 0)) by
          funext ℓ
          by_cases h : (N:ℤ) < |ℓ|
          · rw [if_pos h, if_pos h, div_eq_mul_one_div]
          · rw [if_neg h, if_neg h, mul_zero]]
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hCt4 N hN) hB0
      linarith
    linarith
  have hsumm : Summable (fun ℓ : ℤ => ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖) :=
    summable_of_sum_le (fun ℓ => norm_nonneg _) hpartial
  have hsummC : Summable (fourierCoeff (⇑(logSine_Ffun N hN1))) := Summable.of_norm hsumm
  have hle : (∑' ℓ : ℤ, ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖)
      ≤ 4 * Real.log N + A * (Ch3 * Real.log N) + B * (Ct4 / N) :=
    hsumm.tsum_le_of_sum_le hpartial
  have hkey : Real.log N ≤ (Real.log N)^2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    nlinarith [hlog2N, hlogN]
  have hfin : 4 * Real.log N + A * (Ch3 * Real.log N) + B * (Ct4 / N)
      ≤ (Ci1 * Ch3 / (2 * Real.pi) + Ci2 * Ct4 / (2 * Real.pi * Real.log 2)
          + 4 / Real.log 2 + 1) * (Real.log N)^2 := by
    have hA' : A * (Ch3 * Real.log N) ≤ Ci1 * Ch3 / (2*Real.pi) * (Real.log N)^2 := by
      calc A * (Ch3 * Real.log N) ≤ (Ci1 * Real.log N / (2*Real.pi)) * (Ch3 * Real.log N) :=
            mul_le_mul_of_nonneg_right hAb (by positivity)
        _ = Ci1 * Ch3 / (2*Real.pi) * (Real.log N)^2 := by ring
    have hB' : B * (Ct4 / N) ≤ Ci2 * Ct4 / (2*Real.pi) * Real.log N := by
      calc B * (Ct4 / N) ≤ (Ci2 * (N:ℝ) * Real.log N / (2*Real.pi)) * (Ct4 / N) :=
            mul_le_mul_of_nonneg_right hBb (by positivity)
        _ = Ci2 * Ct4 / (2*Real.pi) * Real.log N := by
            field_simp
    have hB'' : B * (Ct4 / N) ≤ Ci2 * Ct4 / (2*Real.pi * Real.log 2) * (Real.log N)^2 := by
      refine hB'.trans ?_
      have hK0 : 0 ≤ Ci2 * Ct4 / (2*Real.pi) := by positivity
      calc Ci2 * Ct4 / (2*Real.pi) * Real.log N
          ≤ Ci2 * Ct4 / (2*Real.pi) * ((Real.log N)^2 / Real.log 2) :=
            mul_le_mul_of_nonneg_left hkey hK0
        _ = Ci2 * Ct4 / (2*Real.pi * Real.log 2) * (Real.log N)^2 := by ring
    have h4 : 4 * Real.log N ≤ 4 / Real.log 2 * (Real.log N)^2 := by
      calc 4 * Real.log N ≤ 4 * ((Real.log N)^2 / Real.log 2) :=
            mul_le_mul_of_nonneg_left hkey (by norm_num)
        _ = 4 / Real.log 2 * (Real.log N)^2 := by ring
    nlinarith [hA', hB'', h4, sq_nonneg (Real.log N)]
  refine ⟨fun ℓ => fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ, ?_, ?_⟩
  · exact le_trans hle hfin
  · intro α hα1 hα2
    have hαmem : α ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor
      · linarith [neg_abs_le α, Real.pi_gt_three]
      · linarith [le_abs_self α, Real.pi_gt_three]
    have hpt := has_pointwise_sum_fourier_series_of_summable (T := 2 * Real.pi) hsummC
      (α : AddCircle (2 * Real.pi))
    rw [logSine_Ffun_coe_eq N hN1 hαmem] at hpt
    have hcongr : (fun i : ℤ => fourierCoeff (⇑(logSine_Ffun N hN1)) i
          • fourier i (α : AddCircle (2 * Real.pi)))
        = (fun i : ℤ => fourierCoeff (⇑(logSine_Ffun N hN1)) i
          * Complex.exp (Complex.I * (i:ℂ) * (α:ℂ))) := by
      funext i
      have harg : (2 * (Real.pi : ℂ) * Complex.I * (i:ℂ) * (α:ℂ)) / ((2 * Real.pi : ℝ) : ℂ)
          = Complex.I * (i:ℂ) * (α:ℂ) := by
        push_cast
        field_simp
      rw [smul_eq_mul, fourier_coe_apply, harg]
    rw [hcongr] at hpt
    have hre : (∑' i : ℤ, fourierCoeff (⇑(logSine_Ffun N hN1)) i
        * Complex.exp (Complex.I * (i:ℂ) * (α:ℂ))).re = ufun N α := by
      rw [hpt.tsum_eq, ufunC, Complex.ofReal_re]
    rw [hre, ufun_of_range N hN α hα1 hα2]

end

end Work.FIArea4
