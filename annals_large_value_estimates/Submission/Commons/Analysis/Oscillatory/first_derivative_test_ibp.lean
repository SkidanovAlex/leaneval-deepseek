import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Oscillatory

open MeasureTheory

/-- Auxiliary complex exponential of the phase, `x ↦ exp(I * (t * φ x))`. -/
private noncomputable def Efun (φ : ℝ → ℝ) (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * (φ x : ℂ)))

@[simp] private lemma Efun_norm (φ : ℝ → ℝ) (t x : ℝ) : ‖Efun φ t x‖ = 1 := by
  rw [Efun, show Complex.I * (t * (φ x : ℂ)) = ((t * φ x : ℝ) : ℂ) * Complex.I from by
        push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (t * φ x)

private lemma Efun_hasDerivAt {φ φ' : ℝ → ℝ} {t x : ℝ} (h : HasDerivAt φ (φ' x) x) :
    HasDerivAt (Efun φ t) (Efun φ t x * (Complex.I * (t * (φ' x : ℂ)))) x := by
  have h1 : HasDerivAt (fun y => (φ y : ℂ)) ((φ' x : ℝ) : ℂ) x := h.ofReal_comp
  have h2 : HasDerivAt (fun y => t * (φ y : ℂ)) ((t:ℂ) * (φ' x : ℂ)) x := h1.const_mul (t:ℂ)
  have h3 : HasDerivAt (fun y => Complex.I * (t * (φ y : ℂ)))
      (Complex.I * ((t:ℂ) * (φ' x : ℂ))) x := h2.const_mul Complex.I
  exact h3.cexp

/-- The first derivative test (integration by parts): for `ψ`, `φ` differentiable on `[a,b]`
with `t > 0`,
`‖∫_a^b ψ(x) · I φ'(x) · exp(I t φ(x)) dx‖ ≤ t⁻¹ (‖ψ(a)‖ + ‖ψ(b)‖ + ∫_a^b ‖ψ'(x)‖ dx)`. -/
theorem first_derivative_test_ibp {ψ ψ' : ℝ → ℂ} {φ φ' : ℝ → ℝ} {a b t : ℝ}
    (hab : a ≤ b) (ht : 0 < t)
    (hψ : ∀ x ∈ Set.uIcc a b, HasDerivAt ψ (ψ' x) x)
    (hφ : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (φ' x) x)
    (hψcont : ContinuousOn ψ (Set.uIcc a b))
    (hψ'cont : ContinuousOn ψ' (Set.uIcc a b))
    (hψ'int : IntervalIntegrable (fun x => ‖ψ' x‖) volume a b) :
    ‖∫ x in a..b, ψ x * (Complex.I * (φ' x : ℂ)) * Complex.exp (Complex.I * (t * (φ x : ℂ)))‖
      ≤ t⁻¹ * (‖ψ a‖ + ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖) := by
  have _ : ContinuousOn ψ (Set.uIcc a b) := hψcont
  change ‖∫ x in a..b, ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x‖
      ≤ t⁻¹ * (‖ψ a‖ + ‖ψ b‖ + ∫ x in a..b, ‖ψ' x‖)
  have hφcont : ContinuousOn φ (Set.uIcc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hEcont : ContinuousOn (Efun φ t) (Set.uIcc a b) := by
    unfold Efun
    apply Complex.continuous_exp.comp_continuousOn
    exact continuousOn_const.mul
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφcont))
  by_cases hG : IntervalIntegrable
      (fun x => ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x) volume a b
  · have hA_int : IntervalIntegrable (fun x => ψ' x * Efun φ t x) volume a b := by
      refine IntervalIntegrable.mono_fun hψ'int ?_ ?_
      · exact ((hψ'cont.mul hEcont).aestronglyMeasurable measurableSet_uIcc).mono_set
          Set.uIoc_subset_uIcc
      · exact Filter.Eventually.of_forall (fun x =>
          (by show ‖ψ' x * Efun φ t x‖ ≤ ‖‖ψ' x‖‖
              rw [norm_mul, Efun_norm, mul_one, norm_norm]))
    have hFderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y => ψ y * Efun φ t y)
          (ψ' x * Efun φ t x + t * (ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x)) x := by
      intro x hx
      have hd := (hψ x hx).mul (Efun_hasDerivAt (t := t) (hφ x hx))
      exact hd.congr_deriv (by ring)
    have hF'int : IntervalIntegrable
        (fun x => ψ' x * Efun φ t x + t * (ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x))
        volume a b :=
      hA_int.add (hG.const_mul (t : ℂ))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv hF'int
    have hkey : (∫ x in a..b, ψ' x * Efun φ t x)
          + t * ∫ x in a..b, ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x
        = ψ b * Efun φ t b - ψ a * Efun φ t a := by
      calc (∫ x in a..b, ψ' x * Efun φ t x)
            + t * ∫ x in a..b, ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x
          = (∫ x in a..b, ψ' x * Efun φ t x)
            + ∫ x in a..b, (t : ℂ) * (ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x) := by
              rw [intervalIntegral.integral_const_mul]
        _ = ∫ x in a..b, (ψ' x * Efun φ t x
              + (t : ℂ) * (ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x)) := by
              rw [intervalIntegral.integral_add hA_int (hG.const_mul (t : ℂ))]
        _ = ψ b * Efun φ t b - ψ a * Efun φ t a := by
              rw [hFTC]
    have hJ : ∫ x in a..b, ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x
        = ((t : ℂ))⁻¹ * (ψ b * Efun φ t b - ψ a * Efun φ t a
            - ∫ x in a..b, ψ' x * Efun φ t x) := by
      have hb : (t : ℂ) * (∫ x in a..b, ψ x * (Complex.I * (φ' x : ℂ)) * Efun φ t x)
          = ψ b * Efun φ t b - ψ a * Efun φ t a - ∫ x in a..b, ψ' x * Efun φ t x := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hkey
      rw [← hb, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ne_of_gt ht), one_mul]
    rw [hJ, norm_mul]
    have htinv_norm : ‖((t : ℂ))⁻¹‖ = t⁻¹ := by
      rw [norm_inv, show ‖(t:ℂ)‖ = |t| by simp, abs_of_pos ht]
    rw [htinv_norm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hW1 : ‖∫ x in a..b, ψ' x * Efun φ t x‖ ≤ ∫ x in a..b, ‖ψ' x‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hψ'int
      exact Filter.Eventually.of_forall (fun x _ =>
        (by show ‖ψ' x * Efun φ t x‖ ≤ ‖ψ' x‖
            rw [norm_mul, Efun_norm, mul_one]))
    have hW2 : ‖ψ b * Efun φ t b - ψ a * Efun φ t a - ∫ x in a..b, ψ' x * Efun φ t x‖
        ≤ ‖ψ b‖ + ‖ψ a‖ + ∫ x in a..b, ‖ψ' x‖ := by
      have h1 := norm_sub_le (ψ b * Efun φ t b - ψ a * Efun φ t a)
        (∫ x in a..b, ψ' x * Efun φ t x)
      have h2 := norm_sub_le (ψ b * Efun φ t b) (ψ a * Efun φ t a)
      rw [norm_mul, Efun_norm, mul_one, norm_mul, Efun_norm, mul_one] at h2
      linarith [hW1]
    linarith
  · rw [intervalIntegral.integral_undef hG, norm_zero]
    apply mul_nonneg (le_of_lt (inv_pos_of_pos ht))
    have h2 : (0:ℝ) ≤ ∫ x in a..b, ‖ψ' x‖ :=
      intervalIntegral.integral_nonneg hab (fun u _ => norm_nonneg _)
    have h3 : (0:ℝ) ≤ ‖ψ a‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ ‖ψ b‖ := norm_nonneg _
    linarith

end Commons.Analysis.Oscillatory