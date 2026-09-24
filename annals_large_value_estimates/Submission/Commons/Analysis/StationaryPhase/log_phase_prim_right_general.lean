import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Commons.Analysis.Oscillatory.first_derivative_test_ibp

namespace Commons.Analysis.StationaryPhase

open MeasureTheory Set Complex
open scoped Real Interval Topology

noncomputable section

/-- `‖exp (I * r)‖ = 1` for real `r`. -/
private lemma norm_exp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [show Complex.I * (r : ℂ) = (r : ℂ) * Complex.I from by ring]
  exact Complex.norm_exp_ofReal_mul_I r

/-- Derivative of the log-phase `y ↦ log y - y`. -/
private lemma hasDerivAt_log_sub (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log y - y) (1 / y - 1) y := by
  have h := (Real.hasDerivAt_log hy).sub (hasDerivAt_id y)
  exact h.congr_deriv (by rw [one_div])

/-- The log-phase. -/
private def LPhi : ℝ → ℝ := fun y => Real.log y - y

/-- The derivative of the log-phase. -/
private def LPhi' : ℝ → ℝ := fun y => 1 / y - 1

/-- The reciprocal amplitude `1/(i φ')`. -/
private def LPsi : ℝ → ℂ := fun y => -(Complex.I) * (((y / (1 - y)) : ℝ) : ℂ)

/-- The derivative of `LPsi`. -/
private def LPsi' : ℝ → ℂ := fun y => -(Complex.I) * ((((1 - y)⁻¹) ^ 2 : ℝ) : ℂ)

private lemma LPsi_norm (y : ℝ) : ‖LPsi y‖ = |y / (1 - y)| := by
  rw [LPsi, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact RCLike.norm_ofReal _

private lemma LPsi'_norm (y : ℝ) : ‖LPsi' y‖ = ((1 - y)⁻¹) ^ 2 := by
  rw [LPsi', norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact (RCLike.norm_ofReal _).trans (abs_of_nonneg (sq_nonneg _))

private lemma LPsi_hasDerivAt (x : ℝ) (hx1 : (1 : ℝ) - x ≠ 0) :
    HasDerivAt LPsi (LPsi' x) x := by
  have hdiv : HasDerivAt (fun y : ℝ => y / (1 - y)) (((1 - x)⁻¹) ^ 2) x := by
    have h := (hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hx1
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.one_apply, id_eq]
    rw [inv_pow]
    field_simp
    ring
  unfold LPsi LPsi'
  have hc := hdiv.ofReal_comp.const_mul (-(Complex.I))
  simpa using hc

private lemma inv_hasDerivAt (x : ℝ) (hx1 : (1 : ℝ) - x ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (((1 - x)⁻¹) ^ 2) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).inv hx1
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.one_apply, id_eq]
  rw [inv_pow]
  field_simp
  ring

theorem log_phase_prim_right_general (t z q : ℝ) (ht : 1 ≤ t) (hz : 1 < z) (hzq : z ≤ q) (hq : q ≤ 6) :
    ‖∫ s in z..q, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ min (q - z) (24 * q / (t * (z - 1))) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (0 : ℝ) < z - 1 := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  refine le_min ?_ ?_
  · -- trivial length bound
    have h : ‖∫ s in z..q, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
        ≤ 1 * |q - z| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      exact le_of_eq (norm_exp_I_mul (t * (Real.log x - x)))
    simpa [abs_of_nonneg (sub_nonneg.mpr hzq)] using h
  · -- oscillatory bound
    have hψderiv : ∀ x ∈ Set.uIcc z q, HasDerivAt LPsi (LPsi' x) x := by
      intro x hx
      rw [Set.uIcc_of_le hzq] at hx
      exact LPsi_hasDerivAt x (by linarith [hx.1, hz])
    have hφderiv : ∀ x ∈ Set.uIcc z q, HasDerivAt LPhi (LPhi' x) x := by
      intro x hx
      rw [Set.uIcc_of_le hzq] at hx
      have hx0 : x ≠ 0 := by have : (0:ℝ) < x := lt_of_lt_of_le hz0 hx.1; linarith
      unfold LPhi LPhi'
      exact hasDerivAt_log_sub x hx0
    have hψcont : ContinuousOn LPsi (Set.uIcc z q) := by
      have hcont : ContinuousOn (fun y : ℝ => y / (1 - y)) (Set.uIcc z q) := by
        apply ContinuousOn.div continuousOn_id
        · exact continuousOn_const.sub continuousOn_id
        · intro y hy
          rw [Set.uIcc_of_le hzq] at hy
          linarith [hz, hy.1]
      unfold LPsi
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont)
    have hψ'cont : ContinuousOn LPsi' (Set.uIcc z q) := by
      have hcont : ContinuousOn (fun y : ℝ => ((1 - y)⁻¹) ^ 2) (Set.uIcc z q) := by
        refine (((continuousOn_const.sub continuousOn_id).inv₀ ?_).pow 2)
        intro y hy
        rw [Set.uIcc_of_le hzq] at hy
        show (1 : ℝ) - y ≠ 0
        linarith [hz, hy.1]
      unfold LPsi'
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont)
    have hψ'int : IntervalIntegrable (fun x => ‖LPsi' x‖) volume z q :=
      hψ'cont.norm.intervalIntegrable
    have hibp := Commons.Analysis.Oscillatory.first_derivative_test_ibp
      (ψ := LPsi) (ψ' := LPsi') (φ := LPhi) (φ' := LPhi') hzq ht0
      hψderiv hφderiv hψcont hψ'cont hψ'int
    -- rewrite the integral in the ψ form
    have hcong : ∫ x in z..q, LPsi x * (Complex.I * ((LPhi' x : ℝ) : ℂ))
          * Complex.exp (Complex.I * (t * (LPhi x : ℂ)))
        = ∫ s in z..q, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hzq] at hx
      have hx0 : x ≠ 0 := by have : (0:ℝ) < x := lt_of_lt_of_le hz0 hx.1; linarith
      have hx1 : (1 : ℝ) - x ≠ 0 := by linarith [hz, hx.1]
      have hreal : (x / (1 - x) : ℝ) * (1 / x - 1) = 1 := by
        field_simp
      have hmu : ((x / (1 - x) : ℝ) : ℂ) * ((1 / x - 1 : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, hreal]; simp
      have hII : -(Complex.I) * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      have hmul : LPsi x * (Complex.I * ((LPhi' x : ℝ) : ℂ)) = 1 := by
        unfold LPsi LPhi'
        calc -(Complex.I) * ((x / (1 - x) : ℝ) : ℂ) * (Complex.I * ((1 / x - 1 : ℝ) : ℂ))
            = (-(Complex.I) * Complex.I)
                * (((x / (1 - x) : ℝ) : ℂ) * ((1 / x - 1 : ℝ) : ℂ)) := by ring
          _ = 1 := by rw [hII, one_mul, hmu]
      show LPsi x * (Complex.I * ((LPhi' x : ℝ) : ℂ)) * Complex.exp (Complex.I * (t * (LPhi x : ℂ)))
          = Complex.exp (Complex.I * ((t * (Real.log x - x) : ℝ) : ℂ))
      rw [hmul, one_mul]
      congr 1
      show Complex.I * (t * (LPhi x : ℂ)) = Complex.I * ((t * (Real.log x - x) : ℝ) : ℂ)
      unfold LPhi
      rw [Complex.ofReal_mul]
    rw [hcong] at hibp
    -- bounds on the three terms
    have hnormz : ‖LPsi z‖ = z / (z - 1) := by
      rw [LPsi_norm,
        show z / (1 - z) = -(z / (z - 1)) by rw [show (1:ℝ) - z = -(z - 1) by ring, div_neg],
        abs_neg, abs_of_nonneg (div_nonneg (le_of_lt hz0) (le_of_lt hz1))]
    have hnormq : ‖LPsi q‖ = q / (q - 1) := by
      rw [LPsi_norm,
        show q / (1 - q) = -(q / (q - 1)) by rw [show (1:ℝ) - q = -(q - 1) by ring, div_neg],
        abs_neg, abs_of_nonneg (div_nonneg (le_of_lt (by linarith)) (le_of_lt (by linarith)))]
    have hIntEq : ∫ x in z..q, ‖LPsi' x‖ = 1 / (1 - q) - 1 / (1 - z) := by
      have hnormfun : (fun x => ‖LPsi' x‖) = (fun x => ((1 - x)⁻¹) ^ 2) := by
        funext x; rw [LPsi'_norm]
      rw [hnormfun]
      have hderiv : ∀ x ∈ Set.uIcc z q,
          HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (((1 - x)⁻¹) ^ 2) x := by
        intro x hx
        rw [Set.uIcc_of_le hzq] at hx
        exact inv_hasDerivAt x (by linarith [hz, hx.1])
      have hint : IntervalIntegrable (fun x => ((1 - x)⁻¹) ^ 2) volume z q := by
        have hcont : ContinuousOn (fun x : ℝ => ((1 - x)⁻¹) ^ 2) (Set.uIcc z q) := by
          refine (((continuousOn_const.sub continuousOn_id).inv₀ ?_).pow 2)
          intro y hy
          rw [Set.uIcc_of_le hzq] at hy
          show (1 : ℝ) - y ≠ 0
          linarith [hz, hy.1]
        exact hcont.intervalIntegrable
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      rw [hFTC]
      simp only [one_div]
    have hbound : ‖LPsi z‖ + ‖LPsi q‖ + ∫ x in z..q, ‖LPsi' x‖ ≤ 24 * q / (z - 1) := by
      rw [hnormz, hnormq, hIntEq]
      have hz1ne : z - 1 ≠ 0 := ne_of_gt hz1
      have hq1ne : q - 1 ≠ 0 := by linarith
      have h1z : 1 - z ≠ 0 := by linarith
      have h1q : 1 - q ≠ 0 := by linarith
      have hsum_eq : z / (z - 1) + q / (q - 1) + (1 / (1 - q) - 1 / (1 - z))
          = 2 * z / (z - 1) := by
        field_simp
        ring
      rw [hsum_eq]
      apply div_le_div_of_nonneg_right _ (le_of_lt hz1)
      nlinarith [hzq, hz]
    have hfin : t⁻¹ * (‖LPsi z‖ + ‖LPsi q‖ + ∫ x in z..q, ‖LPsi' x‖)
        ≤ 24 * q / (t * (z - 1)) := by
      calc t⁻¹ * (‖LPsi z‖ + ‖LPsi q‖ + ∫ x in z..q, ‖LPsi' x‖)
          ≤ t⁻¹ * (24 * q / (z - 1)) :=
            mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = 24 * q / (t * (z - 1)) := by
            field_simp
    exact le_trans hibp hfin

end

end Commons.Analysis.StationaryPhase
