import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Oscillatory.first_derivative_test_ibp

namespace Commons.Analysis.StationaryPhase

open MeasureTheory Set Complex
open scoped Real Interval Topology

noncomputable section

/-- The reciprocal of the derivative of the log-phase `h(y) = log y - y`, rescaled by `i`. -/
private def Dfun : ℝ → ℂ := fun y => Complex.I * ((1 / y - 1 : ℝ) : ℂ)

/-- The derivative of `Dfun`. -/
private def D'fun : ℝ → ℂ := fun y => Complex.I * ((-(1 / y ^ 2) : ℝ) : ℂ)

/-- The integration-by-parts amplitude `ψ = A / D`. -/
private def psifun (A : ℝ → ℂ) : ℝ → ℂ := A * Dfun⁻¹

/-- The derivative of `psifun A`. -/
private def psi'fun (A : ℝ → ℂ) : ℝ → ℂ :=
  deriv A * Dfun⁻¹ + A * (fun y => -(D'fun y) / (Dfun y) ^ 2)

private lemma Dfun_norm (y : ℝ) : ‖Dfun y‖ = |1 / y - 1| := by
  rw [Dfun, norm_mul, Complex.norm_I, one_mul]
  exact RCLike.norm_ofReal _

private lemma D'fun_norm (y : ℝ) : ‖D'fun y‖ = 1 / y ^ 2 := by
  rw [D'fun, norm_mul, Complex.norm_I, one_mul]
  have h : ‖((-(1 / y ^ 2) : ℝ) : ℂ)‖ = |-(1 / y ^ 2)| := RCLike.norm_ofReal _
  rw [h, abs_neg, abs_of_nonneg (by positivity)]

private lemma Dfun_hasDerivAt (y : ℝ) (hy : y ≠ 0) : HasDerivAt Dfun (D'fun y) y := by
  unfold Dfun D'fun
  have h1 : HasDerivAt (fun z : ℝ => 1 / z - 1) (-(1 / y ^ 2)) y := by
    have h1 : HasDerivAt (fun z : ℝ => z⁻¹ - 1) (-(y ^ 2)⁻¹) y :=
      (hasDerivAt_inv hy).sub_const 1
    have hf : (fun z : ℝ => 1 / z - 1) = (fun z : ℝ => z⁻¹ - 1) := by
      funext z; rw [one_div]
    rw [hf]
    exact h1.congr_deriv (by rw [one_div])
  have h2 := h1.ofReal_comp
  have h3 := h2.const_mul Complex.I
  simpa using h3

private lemma Dfun_ne_zero {c d : ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hdphi : ∀ y ∈ Set.Icc c d, lam ≤ |1 / y - 1|) {y : ℝ} (hy : y ∈ Set.Icc c d) :
    Dfun y ≠ 0 := by
  intro h
  have h0 : (1 / y - 1 : ℝ) = 0 := by
    rw [Dfun] at h
    have h' : ((1 / y - 1 : ℝ) : ℂ) = 0 := (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
    exact Complex.ofReal_eq_zero.mp h'
  have hb := hdphi y hy
  rw [h0, abs_zero] at hb
  linarith

private lemma psifun_hasDerivAt {A : ℝ → ℂ} (hA : ContDiff ℝ 1 A) {y : ℝ} (hy : y ≠ 0)
    (hDne : Dfun y ≠ 0) :
    HasDerivAt (psifun A) (psi'fun A y) y := by
  have hD : HasDerivAt Dfun (D'fun y) y := Dfun_hasDerivAt y hy
  have hA' : HasDerivAt A (deriv A y) y :=
    (hA.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hDinv := hD.inv hDne
  have hmul := hA'.mul hDinv
  simpa only [psifun, psi'fun, Pi.add_apply, Pi.mul_apply] using hmul

private lemma Dfun_continuousOn {c d : ℝ} (hcd : c ≤ d)
    (hy0 : ∀ y ∈ Set.Icc c d, 0 < y) : ContinuousOn Dfun (Set.uIcc c d) := by
  have hu : ContinuousOn (fun y : ℝ => 1 / y - 1) (Set.Icc c d) := by
    have h1 : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Icc c d) :=
      ContinuousOn.inv₀ continuousOn_id (fun y hy => ne_of_gt (hy0 y hy))
    have h2 : ContinuousOn (fun y : ℝ => (1:ℝ) / y) (Set.Icc c d) := by simpa [one_div] using h1
    exact h2.sub continuousOn_const
  rw [Set.uIcc_of_le hcd]
  change ContinuousOn (fun y : ℝ => Complex.I * ((1 / y - 1 : ℝ) : ℂ)) (Set.Icc c d)
  exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hu)

private lemma D'fun_continuousOn {c d : ℝ} (hcd : c ≤ d)
    (hy0 : ∀ y ∈ Set.Icc c d, 0 < y) : ContinuousOn D'fun (Set.uIcc c d) := by
  have hneg : ContinuousOn (fun y : ℝ => -(1 / y ^ 2)) (Set.Icc c d) := by
    have h1 : ContinuousOn (fun y : ℝ => ((y ^ 2)⁻¹)) (Set.Icc c d) :=
      (continuousOn_id.pow 2).inv₀ (fun y hy => pow_ne_zero 2 (ne_of_gt (hy0 y hy)))
    have h2 : ContinuousOn (fun y : ℝ => -((y ^ 2)⁻¹)) (Set.Icc c d) := h1.neg
    simpa [one_div] using h2
  rw [Set.uIcc_of_le hcd]
  change ContinuousOn (fun y : ℝ => Complex.I * ((-(1 / y ^ 2) : ℝ) : ℂ)) (Set.Icc c d)
  exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hneg)

private lemma psifun_continuousOn {c d : ℝ} {A : ℝ → ℂ} (hcd : c ≤ d)
    (hA : ContDiff ℝ 1 A) (hy0 : ∀ y ∈ Set.Icc c d, 0 < y)
    (hDne : ∀ y ∈ Set.uIcc c d, Dfun y ≠ 0) :
    ContinuousOn (psifun A) (Set.uIcc c d) := by
  have hDcont := Dfun_continuousOn hcd hy0
  have h : ContinuousOn (A * Dfun⁻¹) (Set.uIcc c d) :=
    (hA.continuous.continuousOn).mul (hDcont.inv₀ hDne)
  simpa only [psifun] using h

private lemma psi'fun_continuousOn {c d : ℝ} {A : ℝ → ℂ} (hcd : c ≤ d)
    (hA : ContDiff ℝ 1 A) (hy0 : ∀ y ∈ Set.Icc c d, 0 < y)
    (hDne : ∀ y ∈ Set.uIcc c d, Dfun y ≠ 0) :
    ContinuousOn (psi'fun A) (Set.uIcc c d) := by
  have hDcont := Dfun_continuousOn hcd hy0
  have hD'cont := D'fun_continuousOn hcd hy0
  have hderivA : ContinuousOn (deriv A) (Set.uIcc c d) :=
    (hA.continuous_deriv (by norm_num)).continuousOn
  have hDinv : ContinuousOn Dfun⁻¹ (Set.uIcc c d) := hDcont.inv₀ hDne
  have hsq : ContinuousOn (fun y => (Dfun y) ^ 2) (Set.uIcc c d) := by
    have hfun : (fun y => (Dfun y) ^ 2) = (Dfun * Dfun) := by
      funext y; rw [Pi.mul_apply, pow_two]
    rw [hfun]
    exact hDcont.mul hDcont
  have hterm2 : ContinuousOn (fun y => -(D'fun y) / (Dfun y) ^ 2) (Set.uIcc c d) := by
    have h := hD'cont.neg.div hsq (fun y hy => pow_ne_zero 2 (hDne y hy))
    have hfun : (fun y => -(D'fun y) / (Dfun y) ^ 2) = (-D'fun / fun y => (Dfun y) ^ 2) := by
      funext y; simp [Pi.div_apply, Pi.neg_apply]
    rw [hfun]
    exact h
  have h1 : ContinuousOn (deriv A * Dfun⁻¹) (Set.uIcc c d) := hderivA.mul hDinv
  have h2 : ContinuousOn (A * (fun y => -(D'fun y) / (Dfun y) ^ 2)) (Set.uIcc c d) :=
    (hA.continuous.continuousOn).mul hterm2
  simpa only [psi'fun] using h1.add h2

private lemma psifun_norm_le {c d lam : ℝ} {A : ℝ → ℂ}
    (hlam : 0 < lam) (hAc : ∀ y, ‖A y‖ ≤ 1)
    (hdphi : ∀ y ∈ Set.Icc c d, lam ≤ |1 / y - 1|) {y : ℝ} (hy : y ∈ Set.Icc c d) :
    ‖psifun A y‖ ≤ 1 / lam := by
  have hDge : lam ≤ ‖Dfun y‖ := by rw [Dfun_norm]; exact hdphi y hy
  simp only [psifun, Pi.mul_apply, Pi.inv_apply, norm_mul, norm_inv]
  calc ‖A y‖ * ‖Dfun y‖⁻¹ ≤ 1 * lam⁻¹ :=
        mul_le_mul (hAc y) (inv_anti₀ hlam hDge) (by positivity) (by norm_num)
    _ = 1 / lam := by rw [one_mul, one_div]

private lemma psi'fun_norm_le {c d lam Q : ℝ} {A : ℝ → ℂ}
    (hlam : 0 < lam) (hQ : 0 ≤ Q) (hAc : ∀ y, ‖A y‖ ≤ 1) (hAd : ∀ y, ‖deriv A y‖ ≤ 1)
    (hdphi : ∀ y ∈ Set.Icc c d, lam ≤ |1 / y - 1|)
    (hquad : ∀ y ∈ Set.Icc c d, 1 / y ^ 2 ≤ Q) {y : ℝ} (hy : y ∈ Set.Icc c d) :
    ‖psi'fun A y‖ ≤ 1 / lam + Q / lam ^ 2 := by
  have hDge : lam ≤ ‖Dfun y‖ := by rw [Dfun_norm]; exact hdphi y hy
  have hD'le : ‖D'fun y‖ ≤ Q := by rw [D'fun_norm]; exact hquad y hy
  have hD2 : lam ^ 2 ≤ ‖Dfun y‖ ^ 2 := by
    nlinarith [hDge, hlam, norm_nonneg (Dfun y)]
  simp only [psi'fun, Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
  have h1 : ‖deriv A y * (Dfun y)⁻¹‖ ≤ 1 / lam := by
    rw [norm_mul, norm_inv]
    calc ‖deriv A y‖ * ‖Dfun y‖⁻¹ ≤ 1 * lam⁻¹ :=
          mul_le_mul (hAd y) (inv_anti₀ hlam hDge) (by positivity) (by norm_num)
      _ = 1 / lam := by rw [one_mul, one_div]
  have h2 : ‖A y * (-(D'fun y) / (Dfun y) ^ 2)‖ ≤ Q / lam ^ 2 := by
    rw [norm_mul, norm_div, norm_neg, norm_pow]
    have hdiv : ‖D'fun y‖ / ‖Dfun y‖ ^ 2 ≤ Q / lam ^ 2 := by
      calc ‖D'fun y‖ / ‖Dfun y‖ ^ 2 ≤ Q / ‖Dfun y‖ ^ 2 :=
            div_le_div_of_nonneg_right hD'le (by positivity)
        _ ≤ Q / lam ^ 2 :=
            div_le_div_of_nonneg_left hQ (by positivity) hD2
    calc ‖A y‖ * (‖D'fun y‖ / ‖Dfun y‖ ^ 2) ≤ 1 * (Q / lam ^ 2) :=
          mul_le_mul (hAc y) hdiv (by positivity) (by norm_num)
      _ = Q / lam ^ 2 := by rw [one_mul]
  calc ‖deriv A y * (Dfun y)⁻¹ + A y * (-(D'fun y) / (Dfun y) ^ 2)‖
      ≤ ‖deriv A y * (Dfun y)⁻¹‖ + ‖A y * (-(D'fun y) / (Dfun y) ^ 2)‖ := norm_add_le _ _
    _ ≤ 1 / lam + Q / lam ^ 2 := add_le_add h1 h2

theorem logphase_outer_bound_general {A : ℝ → ℂ} {c d t lam Q : ℝ}
    (hcd : c ≤ d) (ht : 0 < t) (hlam : 0 < lam) (hQ : 0 ≤ Q)
    (hA : ContDiff ℝ 1 A)
    (hAc : ∀ y, ‖A y‖ ≤ 1)
    (hAd : ∀ y, ‖deriv A y‖ ≤ 1)
    (hdphi : ∀ y ∈ Set.Icc c d, lam ≤ |1 / y - 1|)
    (hy0 : ∀ y ∈ Set.Icc c d, 0 < y)
    (hquad : ∀ y ∈ Set.Icc c d, 1 / y ^ 2 ≤ Q) :
    ‖∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y))‖
      ≤ t⁻¹ * (2 / lam + (d - c) * (1 / lam + Q / lam ^ 2)) := by
  have hDne : ∀ y ∈ Set.uIcc c d, Dfun y ≠ 0 := by
    intro y hy
    rw [Set.uIcc_of_le hcd] at hy
    exact Dfun_ne_zero hlam hdphi hy
  have hφderiv : ∀ x ∈ Set.uIcc c d,
      HasDerivAt (fun y : ℝ => Real.log y - y) (1 / x - 1) x := by
    intro x hx
    rw [Set.uIcc_of_le hcd] at hx
    have hx0 : x ≠ 0 := ne_of_gt (hy0 x hx)
    have h1 : HasDerivAt (fun y : ℝ => Real.log y - y) (x⁻¹ - 1) x :=
      (Real.hasDerivAt_log hx0).sub (hasDerivAt_id x)
    exact h1.congr_deriv (by rw [one_div])
  have hψderiv : ∀ x ∈ Set.uIcc c d, HasDerivAt (psifun A) (psi'fun A x) x := by
    intro x hx
    have hxI : x ∈ Set.Icc c d := by rwa [Set.uIcc_of_le hcd] at hx
    exact psifun_hasDerivAt hA (ne_of_gt (hy0 x hxI)) (hDne x hx)
  have hψcont : ContinuousOn (psifun A) (Set.uIcc c d) :=
    psifun_continuousOn hcd hA hy0 hDne
  have hψ'cont : ContinuousOn (psi'fun A) (Set.uIcc c d) :=
    psi'fun_continuousOn hcd hA hy0 hDne
  have hψ'int : IntervalIntegrable (fun x => ‖psi'fun A x‖) volume c d :=
    hψ'cont.norm.intervalIntegrable
  have hibp := Commons.Analysis.Oscillatory.first_derivative_test_ibp
      (ψ := psifun A) (ψ' := psi'fun A) (φ := fun y : ℝ => Real.log y - y)
      (φ' := fun y : ℝ => 1 / y - 1) hcd ht hψderiv hφderiv hψcont hψ'cont hψ'int
  have hcong : (∫ x in c..d, psifun A x * (Complex.I * ((1 / x - 1 : ℝ) : ℂ))
        * Complex.exp (Complex.I * (t * ((Real.log x - x : ℝ) : ℂ))))
      = ∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hcd] at hy
    have hDne_y : Dfun y ≠ 0 := Dfun_ne_zero hlam hdphi hy
    have hpsi : psifun A y * (Complex.I * ((1 / y - 1 : ℝ) : ℂ)) = A y := by
      have hDv : Complex.I * ((1 / y - 1 : ℝ) : ℂ) = Dfun y := rfl
      rw [hDv, psifun, Pi.mul_apply, Pi.inv_apply, mul_assoc, inv_mul_cancel₀ hDne_y, mul_one]
    have hexp : Complex.exp (Complex.I * (t * ((Real.log y - y : ℝ) : ℂ)))
        = Complex.exp (Complex.I * t * (Real.log y - y)) := by
      congr 1
      push_cast
      ring
    show psifun A y * (Complex.I * ((1 / y - 1 : ℝ) : ℂ))
        * Complex.exp (Complex.I * (t * ((Real.log y - y : ℝ) : ℂ)))
      = A y * Complex.exp (Complex.I * t * (Real.log y - y))
    rw [hpsi, hexp]
  rw [hcong] at hibp
  have hψc : ‖psifun A c‖ ≤ 1 / lam := psifun_norm_le hlam hAc hdphi ⟨le_refl c, hcd⟩
  have hψd : ‖psifun A d‖ ≤ 1 / lam := psifun_norm_le hlam hAc hdphi ⟨hcd, le_refl d⟩
  have hint : ∫ x in c..d, ‖psi'fun A x‖ ≤ (d - c) * (1 / lam + Q / lam ^ 2) := by
    have hb : ∀ x ∈ Set.Icc c d, ‖psi'fun A x‖ ≤ 1 / lam + Q / lam ^ 2 :=
      fun x hx => psi'fun_norm_le hlam hQ hAc hAd hdphi hquad hx
    have hMint : IntervalIntegrable (fun _ : ℝ => 1 / lam + Q / lam ^ 2) volume c d :=
      intervalIntegrable_const
    have hres := intervalIntegral.integral_mono_on hcd hψ'int hMint hb
    have hval : (∫ _ in c..d, (1 / lam + Q / lam ^ 2))
        = (d - c) * (1 / lam + Q / lam ^ 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rwa [hval] at hres
  calc ‖∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y))‖
      ≤ t⁻¹ * (‖psifun A c‖ + ‖psifun A d‖ + ∫ x in c..d, ‖psi'fun A x‖) := hibp
    _ ≤ t⁻¹ * (2 / lam + (d - c) * (1 / lam + Q / lam ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt ht))
        have h2 : ‖psifun A c‖ + ‖psifun A d‖ ≤ 2 / lam := by
          linarith [hψc, hψd, (show (2:ℝ) / lam = 1 / lam + 1 / lam by ring)]
        linarith [h2, hint]

end

end Commons.Analysis.StationaryPhase
