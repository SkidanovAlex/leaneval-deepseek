import Mathlib
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp
import Submission.Commons.Analysis.Fourier.hausdorff_young_real
import Submission.Commons.Analysis.Fourier.fourierInv_comp_add_eq_modulation

namespace Work.Analysis.Fourier

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology
open Commons.Analysis.CalderonZygmund

noncomputable section

/-- The odd smooth profile `σ t = (2/π) arctan t`, a smooth approximation of the sign
function.  It is odd, `|σ| ≤ 1`, and satisfies the scale invariant Mikhlin bounds
`|t σ' t| ≤ 1` and `|t|² |σ'' t| ≤ 2`. -/
def sigP (t : ℝ) : ℝ := (2 / Real.pi) * Real.arctan t

/-- The Mikhlin symbol `ξ ↦ σ (R ξ)`, extended to `ℂ`. -/
def mSig (R ξ : ℝ) : ℂ := (sigP (R * ξ) : ℂ)

/-- The (complex valued) sign function, `sign 0 = 0`. -/
def sgnC (ξ : ℝ) : ℂ := (Real.sign ξ : ℂ)

/-- The modulation character `x ↦ e^{2πi a x}`. -/
def modFun (a : ℝ) : ℝ → ℂ := fun x => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)

lemma sigP_abs_le_one (t : ℝ) : |sigP t| ≤ 1 := by
  have hpi : (0:ℝ) < 2 / Real.pi := by positivity
  have h1 : |Real.arctan t| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan t), le_of_lt (Real.arctan_lt_pi_div_two t)⟩
  have h2 : |sigP t| = (2 / Real.pi) * |Real.arctan t| := by
    rw [sigP, abs_mul, abs_of_pos hpi]
  rw [h2]
  calc (2 / Real.pi) * |Real.arctan t| ≤ (2 / Real.pi) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left h1 hpi.le
    _ = 1 := by field_simp

lemma sigP_neg (t : ℝ) : sigP (-t) = -sigP t := by
  rw [sigP, sigP, Real.arctan_neg]; ring

lemma sigP_zero : sigP 0 = 0 := by
  rw [sigP, Real.arctan_zero]; ring

lemma deriv_sigP (t : ℝ) : deriv sigP t = (2 / Real.pi) * (1 + t^2)⁻¹ := by
  have h : sigP = fun t : ℝ => (2 / Real.pi) * Real.arctan t := rfl
  rw [h, deriv_const_mul _ (Real.differentiable_arctan.differentiableAt), Real.deriv_arctan]
  simp [one_div]

lemma deriv_sigP_bound (t : ℝ) : |t| * |deriv sigP t| ≤ 1 := by
  have hpi : (0:ℝ) < 2 / Real.pi := by positivity
  have hpos : (0:ℝ) < 1 + t^2 := by positivity
  have hinv : (0:ℝ) < (1 + t^2)⁻¹ := by positivity
  rw [deriv_sigP, abs_mul, abs_of_pos hpi, abs_of_pos hinv]
  have h2 : |t| / (1 + t^2) ≤ 1/2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have h3 : |t| * ((2 / Real.pi) * (1 + t^2)⁻¹) = (2 / Real.pi) * (|t| / (1 + t^2)) := by
    rw [div_eq_mul_inv]; ring
  rw [h3]
  calc (2 / Real.pi) * (|t| / (1 + t^2)) ≤ (2 / Real.pi) * (1/2) :=
        mul_le_mul_of_nonneg_left h2 hpi.le
    _ = 1 / Real.pi := by ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < Real.pi)]
        linarith [Real.pi_gt_three]

lemma differentiableAt_inv_one_add_sq (t : ℝ) : DifferentiableAt ℝ (fun t : ℝ => (1 + t^2)⁻¹) t := by
  have hid : HasDerivAt (fun t : ℝ => 1 + t^2) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  have hfun : (fun t : ℝ => (1 + t^2)⁻¹) = (fun t : ℝ => 1 + t^2)⁻¹ := by funext; simp
  rw [hfun]
  exact (hid.inv (by positivity : (1:ℝ) + t^2 ≠ 0)).differentiableAt

lemma deriv_inv_one_add_sq (t : ℝ) :
    deriv (fun t : ℝ => (1 + t^2)⁻¹) t = -(2*t) * (1 + t^2)⁻¹ * (1 + t^2)⁻¹ := by
  have hid : HasDerivAt (fun t : ℝ => 1 + t^2) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  have hinv := hid.inv (by positivity : (1:ℝ) + t^2 ≠ 0)
  have hfun : (fun t : ℝ => (1 + t^2)⁻¹) = (fun t : ℝ => 1 + t^2)⁻¹ := by funext; simp
  rw [hfun, hinv.deriv]
  field_simp

lemma iteratedDeriv_two_sigP (t : ℝ) :
    iteratedDeriv 2 sigP t = (2 / Real.pi) * (-(2*t) * (1 + t^2)⁻¹ * (1 + t^2)⁻¹) := by
  have hd : deriv sigP = fun t : ℝ => (2 / Real.pi) * (1 + t^2)⁻¹ := funext deriv_sigP
  have h2 : (2:ℕ) = 1 + 1 := rfl
  rw [h2, iteratedDeriv_succ, iteratedDeriv_one, hd,
      deriv_const_mul _ (differentiableAt_inv_one_add_sq t)]
  rw [deriv_inv_one_add_sq t]

lemma iteratedDeriv_two_sigP_bound (t : ℝ) : |t|^2 * |iteratedDeriv 2 sigP t| ≤ 2 := by
  have hpi : (0:ℝ) < 2 / Real.pi := by positivity
  have hpos : (0:ℝ) < 1 + t^2 := by positivity
  have hinv : (0:ℝ) < (1 + t^2)⁻¹ := by positivity
  have habs : |iteratedDeriv 2 sigP t| =
      (2 / Real.pi) * (2 * |t| * (1 + t^2)⁻¹ * (1 + t^2)⁻¹) := by
    rw [iteratedDeriv_two_sigP]
    simp only [abs_mul, abs_neg, abs_of_pos hpi, abs_of_pos hinv,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [habs]
  have hkey : |t|^3 ≤ (1 + t^2)^2 := by
    rcases le_total |t| 1 with h | h
    · have h2 : |t|^3 ≤ 1 := pow_le_one₀ (abs_nonneg t) h
      have h3 : (1:ℝ) ≤ (1 + t^2)^2 := by nlinarith [sq_nonneg t, sq_nonneg (t^2)]
      linarith
    · have h2 : |t|^3 ≤ |t|^4 := pow_le_pow_right₀ h (by norm_num : 3 ≤ 4)
      have h3 : |t|^4 = t^4 := by
        have hh : |t|^4 = (|t|^2)^2 := by ring
        rw [hh, sq_abs]; ring
      calc |t|^3 ≤ |t|^4 := h2
        _ = t^4 := h3
        _ ≤ 1 + 2*t^2 + t^4 := by nlinarith [sq_nonneg t]
        _ = (1 + t^2)^2 := by ring
  have hval : |t|^2 * ((2 / Real.pi) * (2 * |t| * (1 + t^2)⁻¹ * (1 + t^2)⁻¹))
      = (4 / Real.pi) * (|t|^3 / (1 + t^2)^2) := by
    field_simp
    ring
  rw [hval]
  have h4 : (4 / Real.pi) * (|t|^3 / (1 + t^2)^2) ≤ (4 / Real.pi) * 1 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_one (by positivity : (0:ℝ) < (1 + t^2)^2)]
    exact hkey
  have h5 : (4 / Real.pi) ≤ 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi)]
    nlinarith [Real.pi_gt_three]
  linarith

/-! ## The Mikhlin bounds for the profile symbols -/

lemma mSig_contDiff (R : ℝ) : ContDiff ℝ 2 (mSig R) := by
  have h : mSig R = fun ξ : ℝ => ((2 / Real.pi) * Real.arctan (R * ξ) : ℂ) := by
    funext ξ; simp [mSig, sigP]
  rw [h]
  have hlin : ContDiff ℝ 2 (fun ξ : ℝ => R * ξ) := by
    simpa using (contDiff_const (c := R)).mul (contDiff_id (𝕜 := ℝ))
  have hcomp : ContDiff ℝ 2 (fun ξ : ℝ => Real.arctan (R * ξ)) :=
    Real.contDiff_arctan.comp hlin
  have hmul : ContDiff ℝ 2 (fun ξ : ℝ => (2 / Real.pi) * Real.arctan (R * ξ)) :=
    contDiff_const.mul hcomp
  have h2 := Complex.ofRealCLM.contDiff.comp hmul
  have hfun : (⇑Complex.ofRealCLM ∘ fun ξ : ℝ => (2 / Real.pi) * Real.arctan (R * ξ))
      = fun ξ : ℝ => ((2 / Real.pi) * Real.arctan (R * ξ) : ℂ) := by
    funext ξ
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    push_cast
    ring
  rwa [hfun] at h2

lemma continuous_mSig (R : ℝ) : Continuous (mSig R) := mSig_contDiff R |>.continuous

lemma mSig_norm_le (R : ℝ) (ξ : ℝ) : ‖mSig R ξ‖ ≤ 2 := by
  rw [mSig, Complex.norm_real, Real.norm_eq_abs]
  linarith [sigP_abs_le_one (R * ξ)]

lemma mSig_deriv (R : ℝ) (ξ : ℝ) :
    deriv (mSig R) ξ = ((R * deriv sigP (R * ξ) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ sigP (R * ξ) := by
    change DifferentiableAt ℝ (fun t : ℝ => (2 / Real.pi) * Real.arctan t) (R * ξ)
    exact (Real.differentiable_arctan.differentiableAt).const_mul (2 / Real.pi)
  have hsig : HasDerivAt sigP (deriv sigP (R * ξ)) (R * ξ) := hd.hasDerivAt
  have hlin : HasDerivAt (fun ξ : ℝ => R * ξ) R ξ := by
    simpa using (hasDerivAt_id ξ).const_mul R
  have hcomp : HasDerivAt (fun ξ : ℝ => sigP (R * ξ)) (deriv sigP (R * ξ) * R) ξ :=
    hsig.comp ξ hlin
  have hcast : HasDerivAt (fun ξ : ℝ => (sigP (R * ξ) : ℂ)) ((deriv sigP (R * ξ) * R : ℝ) : ℂ) ξ :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt ξ hcomp
  have hkey : deriv (mSig R) ξ = ((deriv sigP (R * ξ) * R : ℝ) : ℂ) := by
    have h : mSig R = fun ξ : ℝ => (sigP (R * ξ) : ℂ) := rfl
    rw [h]
    exact hcast.deriv
  rw [hkey]
  push_cast
  ring

lemma mSig_deriv_bound (R : ℝ) (ξ : ℝ) : |ξ| * ‖deriv (mSig R) ξ‖ ≤ 2 := by
  rw [mSig_deriv, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h : |ξ| * (|R| * |deriv sigP (R * ξ)|) = |R * ξ| * |deriv sigP (R * ξ)| := by
    rw [abs_mul]; ring
  rw [h]
  linarith [deriv_sigP_bound (R * ξ)]

lemma hasDerivAt_deriv_sigP (u : ℝ) : HasDerivAt (deriv sigP) (iteratedDeriv 2 sigP u) u := by
  have key : HasDerivAt (fun t : ℝ => (2 / Real.pi) * (1 + t^2)⁻¹)
      ((2 / Real.pi) * (-(2*u) * (1 + u^2)⁻¹ * (1 + u^2)⁻¹)) u := by
    have hid : HasDerivAt (fun t : ℝ => 1 + t^2) (2*u) u := by
      simpa using (hasDerivAt_pow 2 u).const_add 1
    have hinv := hid.inv (by positivity : (1:ℝ) + u^2 ≠ 0)
    have hfun : (fun t : ℝ => (1 + t^2)⁻¹) = (fun t : ℝ => 1 + t^2)⁻¹ := by funext; simp
    have h2 : HasDerivAt (fun t : ℝ => (1 + t^2)⁻¹) (-(2*u) / (1 + u^2)^2) u := by
      rw [hfun]; exact hinv
    have h3 := h2.const_mul (2 / Real.pi)
    have hval : (2 / Real.pi) * (-(2*u) * (1 + u^2)⁻¹ * (1 + u^2)⁻¹)
        = (2 / Real.pi) * (-(2*u) / (1 + u^2)^2) := by
      field_simp
    rw [hval]
    exact h3
  have hd : deriv sigP = fun t : ℝ => (2 / Real.pi) * (1 + t^2)⁻¹ := funext deriv_sigP
  rw [hd, iteratedDeriv_two_sigP]
  exact key

lemma mSig_iteratedDeriv_two (R : ℝ) (ξ : ℝ) :
    iteratedDeriv 2 (mSig R) ξ = ((R^2 * iteratedDeriv 2 sigP (R * ξ) : ℝ) : ℂ) := by
  have hm : deriv (mSig R) = fun ξ : ℝ => ((R * deriv sigP (R * ξ) : ℝ) : ℂ) :=
    funext (mSig_deriv R)
  have h2 : (2:ℕ) = 1 + 1 := rfl
  rw [h2, iteratedDeriv_succ, iteratedDeriv_one, hm]
  have hbase : HasDerivAt (deriv sigP) (iteratedDeriv 2 sigP (R * ξ)) (R * ξ) :=
    hasDerivAt_deriv_sigP (R * ξ)
  have hlin : HasDerivAt (fun ξ : ℝ => R * ξ) R ξ := by
    simpa using (hasDerivAt_id ξ).const_mul R
  have hcomp : HasDerivAt (fun ξ : ℝ => deriv sigP (R * ξ)) (iteratedDeriv 2 sigP (R * ξ) * R) ξ :=
    hbase.comp ξ hlin
  have hcomp2 : HasDerivAt (fun ξ : ℝ => R * deriv sigP (R * ξ))
      (R * (iteratedDeriv 2 sigP (R * ξ) * R)) ξ := hcomp.const_mul R
  have hcast : HasDerivAt (fun ξ : ℝ => ((R * deriv sigP (R * ξ) : ℝ) : ℂ))
      (((R * (iteratedDeriv 2 sigP (R * ξ) * R) : ℝ)) : ℂ) ξ :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt ξ hcomp2
  rw [hcast.deriv]
  push_cast
  ring

lemma mSig_iteratedDeriv_two_bound (R : ℝ) (ξ : ℝ) :
    |ξ|^2 * ‖iteratedDeriv 2 (mSig R) ξ‖ ≤ 2 := by
  rw [mSig_iteratedDeriv_two, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
  have h : |ξ|^2 * (|R|^2 * |iteratedDeriv 2 sigP (R * ξ)|)
      = |R * ξ|^2 * |iteratedDeriv 2 sigP (R * ξ)| := by
    rw [abs_mul]; ring
  rw [h]
  linarith [iteratedDeriv_two_sigP_bound (R * ξ)]

lemma mikhlin_bounds_arctan_local (R : ℝ) :
    ContDiff ℝ 2 (mSig R) ∧
    (∀ ξ : ℝ, ‖mSig R ξ‖ ≤ 2) ∧
    (∀ ξ : ℝ, |ξ| * ‖deriv (mSig R) ξ‖ ≤ 2) ∧
    (∀ ξ : ℝ, |ξ|^2 * ‖iteratedDeriv 2 (mSig R) ξ‖ ≤ 2) :=
  ⟨mSig_contDiff R, mSig_norm_le R, mSig_deriv_bound R, mSig_iteratedDeriv_two_bound R⟩

/-! ## Convergence of the symbol family to the sign -/

lemma tendsto_sigP_pos {ξ : ℝ} (hξ : 0 < ξ) :
    Tendsto (fun N : ℕ => sigP (((N:ℝ) + 1) * ξ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun N : ℕ => ((N:ℝ) + 1) * ξ) atTop atTop :=
    (tendsto_atTop_add_const_right (atTop : Filter ℕ) (1:ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hξ
  have h2 : Tendsto (fun N : ℕ => Real.arctan (((N:ℝ) + 1) * ξ)) atTop (𝓝 (Real.pi/2)) :=
    (Real.tendsto_arctan_atTop.comp h1).mono_right nhdsWithin_le_nhds
  have h3 : Tendsto (fun N : ℕ => (2/Real.pi) * Real.arctan (((N:ℝ) + 1) * ξ)) atTop
      (𝓝 ((2/Real.pi) * (Real.pi/2))) := h2.const_mul (2/Real.pi)
  have h4 : (2/Real.pi) * (Real.pi/2) = 1 := by
    rw [div_mul_div_comm, mul_comm Real.pi 2,
      div_self (by positivity : (2 * Real.pi) ≠ 0)]
  rw [h4] at h3
  simpa [sigP] using h3

lemma tendsto_mSig (ξ : ℝ) :
    Tendsto (fun N : ℕ => mSig ((N:ℝ) + 1) ξ) atTop (𝓝 (sgnC ξ)) := by
  rcases lt_trichotomy ξ 0 with h | h | h
  · have hpos : 0 < -ξ := by linarith
    have h1 : Tendsto (fun N : ℕ => sigP (((N:ℝ) + 1) * (-ξ))) atTop (𝓝 1) := tendsto_sigP_pos hpos
    have h2 : Tendsto (fun N : ℕ => -sigP (((N:ℝ) + 1) * (-ξ))) atTop (𝓝 (-1)) := h1.neg
    have h3 := (Complex.continuous_ofReal.tendsto (-1:ℝ)).comp h2
    have hfun : (fun N : ℕ => mSig ((N:ℝ) + 1) ξ) =
        fun N : ℕ => ((-sigP (((N:ℝ) + 1) * (-ξ)) : ℝ) : ℂ) := by
      funext N
      rw [mSig, show ((N:ℝ) + 1) * ξ = -(((N:ℝ) + 1) * (-ξ)) by ring, sigP_neg]
    rw [hfun, show sgnC ξ = ((-1:ℝ) : ℂ) by rw [sgnC, Real.sign_of_neg h]]
    exact h3
  · subst h
    rw [show sgnC (0:ℝ) = 0 by rw [sgnC, Real.sign_zero]; exact Complex.ofReal_zero]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with N
    rw [mSig, mul_zero, sigP_zero]
    exact Complex.ofReal_zero
  · have h1 : Tendsto (fun N : ℕ => sigP (((N:ℝ) + 1) * ξ)) atTop (𝓝 1) := tendsto_sigP_pos h
    have h3 := (Complex.continuous_ofReal.tendsto (1:ℝ)).comp h1
    have hfun : (fun N : ℕ => mSig ((N:ℝ) + 1) ξ) =
        fun N : ℕ => ((sigP (((N:ℝ) + 1) * ξ) : ℝ) : ℂ) := by
      funext N; rw [mSig]
    rw [hfun, show sgnC ξ = ((1:ℝ) : ℂ) by rw [sgnC, Real.sign_of_pos h]]
    exact h3


/-! ## Measurability and integrability of the sign, and of modulated Fourier transforms -/

lemma norm_sgnC_le_one (ξ : ℝ) : ‖sgnC ξ‖ ≤ 1 := by
  rcases Real.sign_apply_eq ξ with h | h | h
  · rw [sgnC, h]; norm_num
  · rw [sgnC, h]; norm_num
  · rw [sgnC, h]; norm_num

lemma measurable_sgnC : Measurable sgnC := by
  have hsign : Measurable (Real.sign : ℝ → ℝ) := by
    have h : (Real.sign : ℝ → ℝ) = fun x => if x < 0 then (-1:ℝ) else if 0 < x then 1 else 0 := by
      funext x
      by_cases h1 : x < 0
      · rw [if_pos h1, Real.sign_of_neg h1]
      · rw [if_neg h1]
        by_cases h2 : 0 < x
        · rw [if_pos h2, Real.sign_of_pos h2]
        · rw [if_neg h2, Real.sign_eq_zero_iff.mpr
            (le_antisymm (le_of_not_gt h2) (le_of_not_gt h1))]
    rw [h]
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const)
  have hcoe : sgnC = fun x : ℝ => ((Real.sign x : ℝ) : ℂ) := rfl
  rw [hcoe]
  exact Complex.continuous_ofReal.measurable.comp hsign

lemma integrable_schwartz_fourier (G : SchwartzMap ℝ ℂ) :
    Integrable (FourierTransform.fourier (G : ℝ → ℂ)) volume := by
  rw [(SchwartzMap.fourier_coe G).symm]
  exact SchwartzMap.integrable (FourierTransform.fourier G)

/-- The inverse Fourier transform of an integrable function is continuous. -/
lemma fourierInv_continuous_of_integrable {m : ℝ → ℂ} (hm : Integrable m volume) :
    Continuous (fun x : ℝ => FourierTransformInv.fourierInv m x) := by
  have hc : Continuous (fun x : ℝ => FourierTransform.fourier m x) :=
    Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable hm
  have h : (fun x : ℝ => FourierTransformInv.fourierInv m x)
      = fun x => FourierTransform.fourier m (-x) := by
    funext x; exact Real.fourierInv_eq_fourier_neg m x
  rw [h]
  exact hc.comp continuous_neg

/-- `𝓕⁻ A x` is the integral of `czE x ξ • A ξ`. -/
lemma fourierInv_czE (A : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv A x = ∫ ξ : ℝ, czE x ξ • A ξ := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.inner_apply, czE]
  congr 1
  push_cast
  ring

lemma integral_czE_smul_eq (f g : ℝ → ℂ) (x : ℝ) :
    (∫ ξ : ℝ, (f ξ * czE x ξ) • g ξ)
      = FourierTransformInv.fourierInv (fun ξ : ℝ => f ξ * g ξ) x := by
  rw [fourierInv_czE]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  ring

lemma integrable_sgnC_shift_mul (b x : ℝ) (G : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => (sgnC (ξ + b) * czE x ξ)
      * FourierTransform.fourier (G : ℝ → ℂ) ξ) volume := by
  refine (integrable_schwartz_fourier G).bdd_mul (c := 1) ?_ ?_
  · exact ((measurable_sgnC.comp (measurable_id.add_const b)).mul
      (continuous_czE x).measurable).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul, norm_czE, mul_one]
    exact norm_sgnC_le_one _

/-- If `m` is bounded by `1`, the multiplier operator `𝓕⁻ (m · 𝓕G(· - a))` is continuous. -/
lemma continuous_fourierInv_bdd_mul (m : ℝ → ℂ) (G : SchwartzMap ℝ ℂ) (a : ℝ)
    (hm : AEStronglyMeasurable m volume) (hmb : ∀ ξ : ℝ, ‖m ξ‖ ≤ 1) :
    Continuous (fun x : ℝ => FourierTransformInv.fourierInv
      (fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) (ξ - a)) x) :=
  fourierInv_continuous_of_integrable
    (((integrable_schwartz_fourier G).comp_sub_right a).bdd_mul (c := 1) hm
      (Filter.Eventually.of_forall hmb))

lemma continuous_fourierInv_sign_shift (b : ℝ) (G : SchwartzMap ℝ ℂ) :
    Continuous (fun x : ℝ => FourierTransformInv.fourierInv
      (fun ξ : ℝ => sgnC (ξ + b) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x) := by
  have h := continuous_fourierInv_bdd_mul (fun ξ : ℝ => sgnC (ξ + b)) G 0
    ((measurable_sgnC.comp (measurable_id.add_const b)).aestronglyMeasurable)
    (fun ξ => norm_sgnC_le_one (ξ + b))
  simpa using h

/-- ENNReal arithmetic: `(1/2) * X + (1/2) * X = X`. -/
lemma ofReal_half_mul_add_self (X : ℝ≥0∞) :
    ENNReal.ofReal (1/2) * X + ENNReal.ofReal (1/2) * X = X := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [← two_mul, h2, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.ofReal_one, one_mul]

/-! ## Temperate growth of the modulation -/

lemma modTemp_local (a : ℝ) : Function.HasTemperateGrowth (modFun a) := by
  set c : ℂ := ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I with hc
  have hfun : modFun a = fun x : ℝ => Complex.exp (↑x * c) := by
    funext x; rw [modFun, hc]; congr 1; push_cast; ring
  rw [hfun]
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Complex.exp (↑x * c)) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hderivAt : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (↑x * c))
      (c * Complex.exp (↑x * c)) x := by
    intro x
    have hreal : HasDerivAt (fun y : ℝ => (↑y : ℂ) * c) c x := by
      have h := (hasDerivAt_id x).ofReal_comp
      have h2 := h.mul_const c
      simpa using h2
    have hce := (Complex.hasDerivAt_exp ((↑x : ℂ) * c)).comp x hreal
    rw [show Complex.exp ((↑x : ℂ) * c) * c = c * Complex.exp ((↑x : ℂ) * c) by ring] at hce
    exact hce
  have hderiv : ∀ x : ℝ, deriv (fun x : ℝ => Complex.exp (↑x * c)) x
      = c * Complex.exp (↑x * c) := fun x => (hderivAt x).deriv
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (fun x : ℝ => Complex.exp (↑x * c)) x :=
    fun x => (hderivAt x).differentiableAt
  have hnorm : ∀ x : ℝ, ‖Complex.exp (↑x * c)‖ = 1 := by
    intro x
    have harg : (↑x : ℂ) * c = (↑(2 * Real.pi * a * x) : ℂ) * Complex.I := by
      rw [hc]; push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hiter : ∀ m : ℕ, iteratedDeriv m (fun x : ℝ => Complex.exp (↑x * c))
      = fun x : ℝ => c^m * Complex.exp (↑x * c) := by
    intro m
    induction m with
    | zero => simp [iteratedDeriv_zero]
    | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext x
        rw [deriv_const_mul (c^k) (hdiff x), hderiv x]
        ring
  refine ⟨hcd, fun n => ⟨0, ‖c‖^n, fun x => ?_⟩⟩
  rw [pow_zero, mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter n]
  rw [norm_mul, norm_pow, hnorm x, mul_one]

/-! ## The multiplier bound for the shifted sign -/

lemma sign_shift_bound (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (G : SchwartzMap ℝ ℂ),
      eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
          (fun ξ : ℝ => sgnC (ξ + a) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)
        (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C *
          eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r) (volume : Measure ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp r hr
  refine ⟨C₀ * 2, by positivity, fun a G => ?_⟩
  have htemp : Function.HasTemperateGrowth (modFun a) := modTemp_local a
  set H : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (modFun a) G with hH
  have hHcoe : (H : ℝ → ℂ) = fun x : ℝ => modFun a x • (G : ℝ → ℂ) x := by
    rw [hH, SchwartzMap.smulLeftCLM_apply htemp]
  have hmodnorm : ∀ x : ℝ, ‖modFun a x‖ = 1 :=
    fun x => Complex.norm_exp_ofReal_mul_I (2 * Real.pi * a * x)
  have hHnorm : ∀ x : ℝ, ‖(H : ℝ → ℂ) x‖ = ‖(G : ℝ → ℂ) x‖ := by
    intro x
    rw [congrFun hHcoe x, norm_smul, hmodnorm x, one_mul]
  have hFH : ∀ ξ : ℝ, FourierTransform.fourier (H : ℝ → ℂ) ξ
      = FourierTransform.fourier (G : ℝ → ℂ) (ξ - a) := by
    intro ξ
    have hfun : (H : ℝ → ℂ) = fun x : ℝ => (G : ℝ → ℂ) x * modFun a x := by
      rw [hHcoe]; funext x; rw [smul_eq_mul, mul_comm]
    rw [hfun]
    exact Commons.Analysis.Fourier.fourier_mul_exp_rule (G : ℝ → ℂ) a ξ
  set u : ℕ → ℝ → ℂ := fun N x => ∫ ξ : ℝ,
      (mSig ((N:ℝ) + 1) ξ * czE x ξ)
        • FourierTransform.fourier (G : ℝ → ℂ) (ξ - a) with hu
  set U : ℝ → ℂ := fun x => ∫ ξ : ℝ,
      (sgnC ξ * czE x ξ) • FourierTransform.fourier (G : ℝ → ℂ) (ξ - a) with hU
  have hbound : ∀ N : ℕ, eLpNorm (u N) (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal (C₀ * 2) *
          eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r) (volume : Measure ℝ) := by
    intro N
    obtain ⟨hcd, h1, h2, h3⟩ := mikhlin_bounds_arctan_local ((N:ℝ) + 1)
    have hm := hC₀ (mSig ((N:ℝ) + 1)) 2 (by norm_num) hcd h1 h2 h3 H
    have h1' : (fun x : ℝ => ∫ ξ : ℝ,
        (mSig ((N:ℝ) + 1) ξ * Complex.exp (2 * ↑Real.pi * Complex.I * (↑x * ↑ξ)))
          • FourierTransform.fourier (H : ℝ → ℂ) ξ) = u N := by
      funext x
      rw [hu]
      simp only [czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [hFH]
    have h2' : eLpNorm (H : ℝ → ℂ) (ENNReal.ofReal r) (volume : Measure ℝ)
        = eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r) (volume : Measure ℝ) :=
      eLpNorm_congr_norm_ae H.continuous.aestronglyMeasurable G.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hHnorm)
    rw [h1', h2'] at hm
    exact hm
  have hcont_u : ∀ N : ℕ, Continuous (u N) := by
    intro N
    have hbase := continuous_fourierInv_bdd_mul (fun ξ : ℝ => mSig ((N:ℝ) + 1) ξ) G a
      ((continuous_mSig _).aestronglyMeasurable)
      (fun ξ => by
        rw [mSig, Complex.norm_real, Real.norm_eq_abs]
        exact sigP_abs_le_one _)
    have hconv : u N = fun x : ℝ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => mSig ((N:ℝ) + 1) ξ
          * FourierTransform.fourier (G : ℝ → ℂ) (ξ - a)) x := by
      funext x
      rw [hu]
      dsimp only
      exact integral_czE_smul_eq (fun ξ => mSig ((N:ℝ) + 1) ξ)
        (fun ξ => FourierTransform.fourier (G : ℝ → ℂ) (ξ - a)) x
    rw [hconv]
    exact hbase
  have hlim : ∀ x : ℝ, Tendsto (fun N : ℕ => u N x) atTop (𝓝 (U x)) := by
    intro x
    have hshift : Integrable (fun ξ : ℝ => FourierTransform.fourier (G : ℝ → ℂ) (ξ - a))
        volume := (integrable_schwartz_fourier G).comp_sub_right a
    have hcontG : Continuous (fun ξ : ℝ => FourierTransform.fourier (G : ℝ → ℂ) ξ) :=
      Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable
        (f := (G : ℝ → ℂ)) (SchwartzMap.integrable G)
    rw [hu, hU]
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun ξ : ℝ => ‖FourierTransform.fourier (G : ℝ → ℂ) (ξ - a)‖) ?_ hshift.norm ?_ ?_
    · intro N
      exact (((continuous_mSig _).mul (continuous_czE x)).smul
        (hcontG.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
    · intro N
      filter_upwards with ξ
      rw [norm_smul, norm_mul, norm_czE, mul_one]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [mSig, Complex.norm_real, Real.norm_eq_abs]
        exact sigP_abs_le_one _)
    · filter_upwards with ξ
      have h2 : Tendsto (fun N : ℕ => mSig ((N:ℝ) + 1) ξ * czE x ξ) atTop
          (𝓝 (sgnC ξ * czE x ξ)) := (tendsto_mSig ξ).mul_const (czE x ξ)
      have h3 := h2.mul_const (FourierTransform.fourier (G : ℝ → ℂ) (ξ - a))
      simpa only [smul_eq_mul] using h3
  have hmain : eLpNorm U (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal (C₀ * 2) *
          eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r) (volume : Measure ℝ) :=
    Commons.Analysis.Fourier.eLpNorm_le_of_tendsto_ae (g := U) (gN := u) (p := r)
      (by linarith) (fun N => (hcont_u N).aestronglyMeasurable)
      (Filter.Eventually.of_forall hlim) hbound
  have hUA : ∀ x : ℝ, FourierTransformInv.fourierInv
      (fun ξ : ℝ => sgnC ξ * FourierTransform.fourier (G : ℝ → ℂ) (ξ - a)) x = U x := by
    intro x
    rw [hU]
    exact (integral_czE_smul_eq sgnC
      (fun ξ => FourierTransform.fourier (G : ℝ → ℂ) (ξ - a)) x).symm
  have hE : ∀ x : ℝ,
      ‖Complex.exp (-(2 * Real.pi * Complex.I * ((a * x : ℝ) : ℂ)))‖ = 1 := by
    intro x
    have harg : -(2 * Real.pi * Complex.I * ((a * x : ℝ) : ℂ))
        = ((-(2 * Real.pi * (a * x)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  set A : ℝ → ℂ := fun η : ℝ => sgnC η
      * FourierTransform.fourier (G : ℝ → ℂ) (η - a) with hA
  have hnorm_eq : eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => sgnC (ξ + a) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)
        (ENNReal.ofReal r) (volume : Measure ℝ)
      = eLpNorm U (ENNReal.ofReal r) (volume : Measure ℝ) := by
    have h1 : (fun ξ : ℝ => sgnC (ξ + a) * FourierTransform.fourier (G : ℝ → ℂ) ξ)
        = fun ξ : ℝ => A (ξ + a) := by
      funext ξ; simp only [hA, add_sub_cancel_right]
    have hUm : AEStronglyMeasurable U (volume : Measure ℝ) :=
      aestronglyMeasurable_of_tendsto_ae _ (fun N => (hcont_u N).aestronglyMeasurable)
        (Filter.Eventually.of_forall hlim)
    have hfm : AEStronglyMeasurable (fun x : ℝ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => sgnC (ξ + a) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)
        (volume : Measure ℝ) := by
      refine AEStronglyMeasurable.congr (f := fun x : ℝ =>
          Complex.exp (-(2 * Real.pi * Complex.I * ((a * x : ℝ) : ℂ))) * U x)
        (((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul hUm)
        (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [h1, Commons.Analysis.Fourier.fourierInv_comp_add_eq_modulation A a x, hUA x]
    refine eLpNorm_congr_norm_ae hfm hUm ?_
    filter_upwards with x
    rw [h1, Commons.Analysis.Fourier.fourierInv_comp_add_eq_modulation A a x, hUA x,
      norm_mul, hE x, one_mul]
  rw [hnorm_eq]
  exact hmain

/-! ## From an `eLpNorm` bound to a `lintegral` bound -/

lemma rpow_one_div_mul_self {r : ℝ} (hr : 0 < r) (X : ℝ≥0∞) : (X ^ (1/r)) ^ r = X := by
  rw [← ENNReal.rpow_mul, show (1/r) * r = 1 by field_simp, ENNReal.rpow_one]

lemma eLpNorm_to_lintegral_local {r : ℝ} (hr : 0 < r) {C : ℝ} (hC : 0 < C) {f g : ℝ → ℂ}
    (h : eLpNorm f (ENNReal.ofReal r) (volume : Measure ℝ)
          ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (volume : Measure ℝ))
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    ∫⁻ x : ℝ, ‖f x‖ₑ ^ r ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ r := by
  have hrne : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB : eLpNorm g (ENNReal.ofReal r) (volume : Measure ℝ)
      = (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrne hrtop hg, ENNReal.toReal_ofReal hr.le]
  by_cases hf : AEStronglyMeasurable f (volume : Measure ℝ)
  swap
  · -- then `eLpNorm f = ∞`, which forces `∫⁻ ‖g‖ₑ ^ r = ∞`
    rw [eLpNorm_of_not_aestronglyMeasurable hf, hB, top_le_iff] at h
    have hC0 : ENNReal.ofReal C ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hC
    have hI : (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) = ⊤ := by
      by_contra hne
      have : ENNReal.ofReal C * (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hne)
      exact this h
    rw [hI, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hC r))]
    exact le_top
  have hA : eLpNorm f (ENNReal.ofReal r) (volume : Measure ℝ)
      = (∫⁻ x : ℝ, ‖f x‖ₑ ^ r) ^ (1/r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrne hrtop hf, ENNReal.toReal_ofReal hr.le]
  rw [hA, hB] at h
  have hpow : ((∫⁻ x : ℝ, ‖f x‖ₑ ^ r) ^ (1/r)) ^ r
      ≤ (ENNReal.ofReal C * (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r)) ^ r :=
    ENNReal.rpow_le_rpow h hr.le
  have hstep : (ENNReal.ofReal C * (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r)) ^ r
      = ENNReal.ofReal (C^r) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ r := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.ofReal_rpow_of_nonneg hC.le hr.le,
      rpow_one_div_mul_self hr]
  rw [rpow_one_div_mul_self hr, hstep] at hpow
  exact hpow

/-- The "sharp" band projection `P f = 𝓕⁻(1_{[-1/2,1/2]}·𝓕f)` is bounded on `L^r(ℝ)` for every `1 < r < ∞` (M. Riesz / the Hilbert transform, the multiplier being the indicator of an interval). Stated for Schwartz functions.

Recommended route (all ingredients exist in this workspace):
* the smoothed odd profile `σ t = smoothTransition t - smoothTransition (-t)`; for each `R > 0`, `m_R ξ = σ (R * ξ)` is `ContDiff ℝ 2` and satisfies the Mikhlin bounds `‖m_R ξ‖ ≤ A`, `|ξ| * ‖deriv m_R ξ‖ ≤ A`, `|ξ|^2 * ‖iteratedDeriv 2 m_R ξ‖ ≤ A` with `A` independent of `R` (because `|t|^k|σ^{(k)} t|` is bounded and scale-invariant);
* `Commons.Analysis.Fourier.mikhlin_multiplier_lp` then gives `P_{m_R}` bounded on `L^r` with norm `≤ C*A` uniformly in `R`;
* `m_R → sign` pointwise as `R → ∞`, so dominated convergence in `∫ ξ, m_R ξ * e^{2πixξ} * 𝓕G ξ dξ` and `Commons.Analysis.Fourier.eLpNorm_le_liminf_of_enorm_le_liminf_of_ae` give the bound for the multiplier `sign`;
* `1_{[-1/2,1/2]}(ξ) = (1/2)(sign (ξ+1/2) - sign (ξ-1/2))` a.e., and `P_{sign(·+a)} = M_{-a} ∘ P_{sign} ∘ M_a` (modulations are `L^r` isometries), so one needs that `x ↦ Complex.exp (2πi a x) * G x` is again a `SchwartzMap` (via `SchwartzMap.smulLeftCLM` and `Function.HasTemperateGrowth (fun x => Complex.exp (2πi a x))`). -/
theorem band_projection_schwartz_lp (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : SchwartzMap ℝ ℂ),
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
            * FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ r
        ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ r := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sign_shift_bound r hr
  refine ⟨C₁, hC₁pos, fun G => ?_⟩
  set Ψp : ℝ → ℂ := fun x => FourierTransformInv.fourierInv
      (fun ξ : ℝ => sgnC (ξ + 1/2) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x with hΨp
  set Ψm : ℝ → ℂ := fun x => FourierTransformInv.fourierInv
      (fun ξ : ℝ => sgnC (ξ - 1/2) * FourierTransform.fourier (G : ℝ → ℂ) ξ) x with hΨm
  have hp_bound : eLpNorm Ψp (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C₁ * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r)
          (volume : Measure ℝ) := by
    rw [hΨp]; exact hC₁ (1/2) G
  have hm_bound : eLpNorm Ψm (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C₁ * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r)
          (volume : Measure ℝ) := by
    rw [hΨm]; exact hC₁ (-(1/2)) G
  have hp_sm : AEStronglyMeasurable Ψp volume := by
    rw [hΨp]; exact (continuous_fourierInv_sign_shift (1/2) G).aestronglyMeasurable
  have hm_sm : AEStronglyMeasurable Ψm volume := by
    rw [hΨm]; exact (continuous_fourierInv_sign_shift (-(1/2)) G).aestronglyMeasurable
  have h1r : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [ENNReal.one_le_ofReal]; linarith
  have hnorm_half : ‖(1/2 : ℂ)‖ₑ = ENNReal.ofReal (1/2) := by
    rw [enorm_eq_ofReal_norm']
    congr 1
    rw [show (1/2 : ℂ) = (1:ℂ)/2 from rfl, norm_div, norm_one, Complex.norm_ofNat]
  -- The a.e. identity relating the indicator to the two shifted signs
  have hpoint : ∀ ξ : ℝ, ξ ≠ 1/2 → ξ ≠ -(1/2) →
      (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
        = (1/2) * (sgnC (ξ + 1/2) - sgnC (ξ - 1/2)) := by
    intro ξ h1 h2
    rcases lt_trichotomy ξ (-(1/2)) with h | h | h
    · have hnot : ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) := fun hx => absurd hx.1 (not_le.mpr h)
      rw [Set.indicator_of_notMem hnot]
      have hp : sgnC (ξ + 1/2) = -1 := by rw [sgnC, Real.sign_of_neg (by linarith)]; norm_num
      have hm : sgnC (ξ - 1/2) = -1 := by rw [sgnC, Real.sign_of_neg (by linarith)]; norm_num
      rw [hp, hm]; norm_num
    · exact absurd h h2
    · rcases lt_trichotomy ξ (1/2) with h' | h' | h'
      · have hmem : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2) := ⟨le_of_lt h, le_of_lt h'⟩
        rw [Set.indicator_of_mem hmem]
        have hp : sgnC (ξ + 1/2) = 1 := by rw [sgnC, Real.sign_of_pos (by linarith)]; norm_num
        have hm : sgnC (ξ - 1/2) = -1 := by rw [sgnC, Real.sign_of_neg (by linarith)]; norm_num
        rw [hp, hm]; norm_num
      · exact absurd h' h1
      · have hnot : ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) := fun hx => absurd hx.2 (not_le.mpr h')
        rw [Set.indicator_of_notMem hnot]
        have hp : sgnC (ξ + 1/2) = 1 := by rw [sgnC, Real.sign_of_pos (by linarith)]; norm_num
        have hm : sgnC (ξ - 1/2) = 1 := by rw [sgnC, Real.sign_of_pos (by linarith)]; norm_num
        rw [hp, hm]; norm_num
  have hmem_ae : ∀ᵐ ξ : ℝ, (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
      = (1/2) * (sgnC (ξ + 1/2) - sgnC (ξ - 1/2)) := by
    have hnull : volume ({ξ : ℝ | ξ = 1/2 ∨ ξ = -(1/2)} : Set ℝ) = 0 := by
      have hfin : ({ξ : ℝ | ξ = 1/2 ∨ ξ = -(1/2)} : Set ℝ).Finite :=
        ((Set.finite_singleton (1/2)).union (Set.finite_singleton (-(1/2)))).subset (by
          intro ξ hξ
          simp only [Set.mem_setOf_eq] at hξ
          simpa only [Set.mem_union, Set.mem_singleton_iff] using hξ)
      exact hfin.measure_zero volume
    have hae : ∀ᵐ ξ : ℝ, ξ ≠ 1/2 ∧ ξ ≠ -(1/2) := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ hnull
      intro ξ hξ
      simp only [Set.mem_setOf_eq] at hξ ⊢
      by_cases h2 : ξ = 1/2
      · exact Or.inl h2
      · refine Or.inr ?_
        by_contra h3
        exact hξ ⟨h2, h3⟩
    filter_upwards [hae] with ξ hξ
    exact hpoint ξ hξ.1 hξ.2
  -- the pointwise identity `Φ = (1/2)(Ψp - Ψm)`
  have hPhi_eq : ∀ x : ℝ, FourierTransformInv.fourierInv
      (fun ξ : ℝ => (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ) x = (1/2) * (Ψp x - Ψm x) := by
    intro x
    have hI : FourierTransformInv.fourierInv
        (fun ξ : ℝ => (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ) x
        = ∫ ξ : ℝ, ((Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
            * czE x ξ) * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      rw [fourierInv_czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul]; ring
    have hP : Ψp x = ∫ ξ : ℝ, (sgnC (ξ + 1/2) * czE x ξ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      rw [hΨp]
      dsimp only
      rw [fourierInv_czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul]; ring
    have hM : Ψm x = ∫ ξ : ℝ, (sgnC (ξ - 1/2) * czE x ξ)
        * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      rw [hΨm]
      dsimp only
      rw [fourierInv_czE]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul]; ring
    rw [hI, hP, hM]
    have h1 : (∫ ξ : ℝ, ((Set.indicator (Set.Icc (-(1/2):ℝ) (1/2))
            (fun _ : ℝ => (1:ℂ)) ξ) * czE x ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ)
        = ∫ ξ : ℝ, ((1/2) * (sgnC (ξ + 1/2) - sgnC (ξ - 1/2)) * czE x ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ := by
      refine integral_congr_ae ?_
      filter_upwards [hmem_ae] with ξ hξ
      rw [hξ]
    rw [h1]
    have h3 : (∫ ξ : ℝ, ((1/2) * (sgnC (ξ + 1/2) - sgnC (ξ - 1/2)) * czE x ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ)
        = ∫ ξ : ℝ, ((1/2) * ((sgnC (ξ + 1/2) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)
            - (1/2) * ((sgnC (ξ - 1/2) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      ring
    rw [h3]
    have hsplit : (∫ ξ : ℝ, ((1/2) * ((sgnC (ξ + 1/2) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)
            - (1/2) * ((sgnC (ξ - 1/2) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)))
        = (∫ ξ : ℝ, (1/2) * ((sgnC (ξ + 1/2) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ))
          - (∫ ξ : ℝ, (1/2) * ((sgnC (ξ - 1/2) * czE x ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ)) :=
      integral_sub ((integrable_sgnC_shift_mul (1/2) x G).const_mul (1/2))
        ((integrable_sgnC_shift_mul (-(1/2)) x G).const_mul (1/2))
    rw [hsplit, integral_const_mul, integral_const_mul]
    ring
  -- the `L^r` bound
  have hbound : eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ) x) (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C₁ * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r)
          (volume : Measure ℝ) := by
    have hsub : (fun x : ℝ => (1/2) * (Ψp x - Ψm x))
        = (1/2 : ℂ) • (fun x : ℝ => Ψp x - Ψm x) := by
      funext x; rw [Pi.smul_apply, smul_eq_mul]
    calc eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
            (fun ξ : ℝ => (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ : ℝ => (1:ℂ)) ξ)
              * FourierTransform.fourier (G : ℝ → ℂ) ξ) x) (ENNReal.ofReal r) (volume : Measure ℝ)
        = eLpNorm (fun x : ℝ => (1/2) * (Ψp x - Ψm x)) (ENNReal.ofReal r) (volume : Measure ℝ) :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall hPhi_eq)
      _ = ‖(1/2 : ℂ)‖ₑ * eLpNorm (fun x : ℝ => Ψp x - Ψm x) (ENNReal.ofReal r)
              (volume : Measure ℝ) := by
          rw [hsub, eLpNorm_const_smul]
      _ = ENNReal.ofReal (1/2) * eLpNorm (fun x : ℝ => Ψp x - Ψm x) (ENNReal.ofReal r)
              (volume : Measure ℝ) := by
          rw [hnorm_half]
      _ ≤ ENNReal.ofReal (1/2) * (eLpNorm Ψp (ENNReal.ofReal r) (volume : Measure ℝ)
            + eLpNorm Ψm (ENNReal.ofReal r) (volume : Measure ℝ)) := by
          gcongr
          exact eLpNorm_sub_le h1r
      _ ≤ ENNReal.ofReal (1/2) * (ENNReal.ofReal C₁ * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x)
              (ENNReal.ofReal r) (volume : Measure ℝ)
            + ENNReal.ofReal C₁ * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x)
              (ENNReal.ofReal r) (volume : Measure ℝ)) := by
          gcongr
      _ = ENNReal.ofReal C₁ * eLpNorm (fun x : ℝ => (G : ℝ → ℂ) x) (ENNReal.ofReal r)
            (volume : Measure ℝ) := by
          rw [mul_add, ofReal_half_mul_add_self]
  exact eLpNorm_to_lintegral_local (by linarith : (0:ℝ) < r) hC₁pos hbound
    G.continuous.aestronglyMeasurable

end

end Work.Analysis.Fourier
