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

theorem log_phase_prim_left_general (t p z : ℝ) (ht : 1 ≤ t) (hp : 1/8 ≤ p) (hpz : p ≤ z) (hz : z < 1) :
    ‖∫ s in p..z, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ min (z - p) (24 / (t * (1 - z))) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hp0 : (0 : ℝ) < p := by linarith
  have hz1 : (0 : ℝ) < 1 - z := by linarith
  have hzp : z < 1 := hz
  refine le_min ?_ ?_
  · -- trivial length bound
    have h : ‖∫ s in p..z, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
        ≤ 1 * |z - p| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      exact le_of_eq (norm_exp_I_mul (t * (Real.log x - x)))
    simpa [abs_of_nonneg (sub_nonneg.mpr hpz)] using h
  · -- oscillatory bound
    have hψderiv : ∀ x ∈ Set.uIcc p z, HasDerivAt LPsi (LPsi' x) x := by
      intro x hx
      rw [Set.uIcc_of_le hpz] at hx
      exact LPsi_hasDerivAt x (by linarith [hx.2, hz])
    have hφderiv : ∀ x ∈ Set.uIcc p z, HasDerivAt LPhi (LPhi' x) x := by
      intro x hx
      rw [Set.uIcc_of_le hpz] at hx
      have hx0 : x ≠ 0 := by have : (0:ℝ) < x := lt_of_lt_of_le hp0 hx.1; linarith
      unfold LPhi LPhi'
      exact hasDerivAt_log_sub x hx0
    have hψcont : ContinuousOn LPsi (Set.uIcc p z) := by
      have hcont : ContinuousOn (fun y : ℝ => y / (1 - y)) (Set.uIcc p z) := by
        apply ContinuousOn.div continuousOn_id
        · exact continuousOn_const.sub continuousOn_id
        · intro y hy
          rw [Set.uIcc_of_le hpz] at hy
          linarith [hz, hy.2]
      unfold LPsi
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont)
    have hψ'cont : ContinuousOn LPsi' (Set.uIcc p z) := by
      have hcont : ContinuousOn (fun y : ℝ => ((1 - y)⁻¹) ^ 2) (Set.uIcc p z) := by
        refine (((continuousOn_const.sub continuousOn_id).inv₀ ?_).pow 2)
        intro y hy
        rw [Set.uIcc_of_le hpz] at hy
        show (1 : ℝ) - y ≠ 0
        linarith [hz, hy.2]
      unfold LPsi'
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont)
    have hψ'int : IntervalIntegrable (fun x => ‖LPsi' x‖) volume p z :=
      hψ'cont.norm.intervalIntegrable
    have hibp := Commons.Analysis.Oscillatory.first_derivative_test_ibp
      (ψ := LPsi) (ψ' := LPsi') (φ := LPhi) (φ' := LPhi') hpz ht0
      hψderiv hφderiv hψcont hψ'cont hψ'int
    -- rewrite the integral in the ψ form
    have hcong : ∫ x in p..z, LPsi x * (Complex.I * ((LPhi' x : ℝ) : ℂ))
          * Complex.exp (Complex.I * (t * (LPhi x : ℂ)))
        = ∫ s in p..z, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hpz] at hx
      have hx0 : x ≠ 0 := by have : (0:ℝ) < x := lt_of_lt_of_le hp0 hx.1; linarith
      have hx1 : (1 : ℝ) - x ≠ 0 := by linarith [hz, hx.2]
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
    have hnormp : ‖LPsi p‖ = p / (1 - p) := by
      rw [LPsi_norm]
      exact abs_of_nonneg (div_nonneg (le_of_lt hp0) (by linarith))
    have hnormz : ‖LPsi z‖ = z / (1 - z) := by
      rw [LPsi_norm]
      exact abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hz1))
    have hIntEq : ∫ x in p..z, ‖LPsi' x‖ = 1 / (1 - z) - 1 / (1 - p) := by
      have hnormfun : (fun x => ‖LPsi' x‖) = (fun x => ((1 - x)⁻¹) ^ 2) := by
        funext x; rw [LPsi'_norm]
      rw [hnormfun]
      have hderiv : ∀ x ∈ Set.uIcc p z,
          HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (((1 - x)⁻¹) ^ 2) x := by
        intro x hx
        rw [Set.uIcc_of_le hpz] at hx
        exact inv_hasDerivAt x (by linarith [hz, hx.2])
      have hint : IntervalIntegrable (fun x => ((1 - x)⁻¹) ^ 2) volume p z := by
        have hcont : ContinuousOn (fun x : ℝ => ((1 - x)⁻¹) ^ 2) (Set.uIcc p z) := by
          refine (((continuousOn_const.sub continuousOn_id).inv₀ ?_).pow 2)
          intro y hy
          rw [Set.uIcc_of_le hpz] at hy
          show (1 : ℝ) - y ≠ 0
          linarith [hz, hy.2]
        exact hcont.intervalIntegrable
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      rw [hFTC]
      simp only [one_div]
    have hbound : ‖LPsi p‖ + ‖LPsi z‖ + ∫ x in p..z, ‖LPsi' x‖ ≤ 24 / (1 - z) := by
      rw [hnormp, hnormz, hIntEq]
      have hz2 : (0:ℝ) ≤ 2 - z := by linarith [hz]
      have hpz2 : p * (2 - z) ≤ z * (2 - z) := mul_le_mul_of_nonneg_right hpz hz2
      have hz2le : z * (2 - z) ≤ 1 := by nlinarith [sq_nonneg (1 - z)]
      have h1 : p / (1 - p) ≤ 1 / (1 - z) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - p), div_mul_eq_mul_div, one_mul,
          le_div_iff₀ hz1]
        nlinarith [hpz2, hz2le]
      have h2 : z / (1 - z) ≤ 1 / (1 - z) := by
        exact div_le_div_of_nonneg_right (by linarith [hz] : z ≤ 1) (le_of_lt hz1)
      have h3 : 1 / (1 - z) - 1 / (1 - p) ≤ 1 / (1 - z) := by
        have : 0 ≤ 1 / (1 - p) := by
          apply div_nonneg zero_le_one; linarith
        linarith
      have hsum : p / (1 - p) + z / (1 - z) + (1 / (1 - z) - 1 / (1 - p)) ≤ 3 / (1 - z) := by
        have he : (3:ℝ) / (1 - z) = 1 / (1 - z) + 1 / (1 - z) + 1 / (1 - z) := by ring
        rw [he]; linarith [h1, h2, h3]
      have h324 : (3:ℝ) / (1 - z) ≤ 24 / (1 - z) := by
        apply div_le_div_of_nonneg_right (by norm_num) (le_of_lt hz1)
      linarith [hsum, h324]
    have hfin : t⁻¹ * (‖LPsi p‖ + ‖LPsi z‖ + ∫ x in p..z, ‖LPsi' x‖) ≤ 24 / (t * (1 - z)) := by
      calc t⁻¹ * (‖LPsi p‖ + ‖LPsi z‖ + ∫ x in p..z, ‖LPsi' x‖)
          ≤ t⁻¹ * (24 / (1 - z)) :=
            mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = 24 / (t * (1 - z)) := by
            field_simp
    exact le_trans hibp hfin

end

end Commons.Analysis.StationaryPhase