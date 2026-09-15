import Mathlib
import Submission.Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.norm_cpow_gam_eq
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Integral.integrable_log_sq_lorentz

namespace Commons.NumberTheory.Zeta

open MeasureTheory
open Commons.Analysis.Complex

noncomputable section

/-! ## Auxiliary lemmas

We bound each factor of the integrand
`‖gamDot β t‖ / (‖ζ(1 + gam β t)‖ * ‖ζ(1 - gam β t)‖ * ‖gam β t‖^4)` separately:

* the two reciprocal zeta factors by `C₁ * (log (|t| + 2) + 1)` (hypothesis `hinvb`, applied
  at `z = gam β t` and `z = -gam β t`, both of which lie in the zero-free region);
* `‖gamDot β t‖` by a constant;
* `1 / ‖gam β t‖^4` by `Cg / (1 + t^2)`.

The resulting dominating function is a constant multiple of
`(log (2 + |t|) + 1)^2 / (1 + t^2)`, which is integrable. -/

/-- `hinvb` applied at `z = gam β t`. -/
private lemma inv_zeta_gam_le {β C₁ : ℝ} (hβ : 0 < β)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1)) (t : ℝ) :
    ‖(riemannZeta (1 + gam β t))⁻¹‖ ≤ C₁ * (Real.log (|t| + 2) + 1) := by
  have h := hinvb (gam β t) (gam_ne_zero hβ t) ?_ ?_
  · rwa [gam_im] at h
  · rw [gam_im, gam_re]
  · rw [gam_re]
    have hlt := phi_lt_c hβ zero_lt_one t
    simp only [phi] at hlt
    linarith

/-- `hinvb` applied at `z = -gam β t`. -/
private lemma inv_zeta_neg_gam_le {β C₁ : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1)) (t : ℝ) :
    ‖(riemannZeta (1 - gam β t))⁻¹‖ ≤ C₁ * (Real.log (|t| + 2) + 1) := by
  have hne : -gam β t ≠ 0 := neg_ne_zero.mpr (gam_ne_zero hβ t)
  have h := hinvb (-gam β t) hne ?_ ?_
  · have heq : (1:ℂ) + (-gam β t) = 1 - gam β t := by ring
    rw [heq] at h
    rwa [Complex.neg_im, abs_neg, gam_im] at h
  · rw [Complex.neg_re, gam_re, Complex.neg_im, abs_neg, gam_im]
    have hnn : 0 ≤ β / Real.log (|t| + 2) :=
      div_nonneg hβ.le (Real.log_nonneg (by have := abs_nonneg t; linarith))
    linarith
  · rw [Complex.neg_re, gam_re]
    have hlogpos : 0 < Real.log (|t| + 2) := Real.log_pos (by have := abs_nonneg t; linarith)
    have hlog2 : (1:ℝ)/10 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogge : Real.log 2 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
    have hlt : β < Real.log (|t| + 2) := lt_of_le_of_lt hβ10 (lt_of_lt_of_le hlog2 hlogge)
    have := (div_lt_one hlogpos).mpr hlt
    linarith

/-- The fourth power of `‖gam β t‖` is bounded below by a constant times `1 + t^2`. -/
private lemma inv_norm_gam_pow4_le {β : ℝ} (hβ : 0 < β) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ t : ℝ, 1 / ‖gam β t‖ ^ 4 ≤ Cg / (1 + t ^ 2) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set e : ℝ := min (β / Real.log 3) 1 with hedef
  have hepos : 0 < e := lt_min (div_pos hβ hlog3) one_pos
  have he4pos : 0 < e ^ 4 := pow_pos hepos 4
  refine ⟨max (2 / e ^ 4) 4, lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro t
  have h1t : 0 < 1 + t ^ 2 := by positivity
  rcases le_or_gt |t| 1 with ht | ht
  · have hgam_ge : e ≤ ‖gam β t‖ := min_div_log_three_one_le_norm_gam hβ t
    have he4 : e ^ 4 ≤ ‖gam β t‖ ^ 4 := pow_le_pow_left₀ hepos.le hgam_ge 4
    have hle : (1:ℝ) / ‖gam β t‖ ^ 4 ≤ 1 / e ^ 4 :=
      one_div_le_one_div_of_le he4pos he4
    have hint : t ^ 2 ≤ 1 := by
      have h := abs_le.mp ht
      nlinarith [h.1, h.2]
    have h2 : 1 + t ^ 2 ≤ 2 := by linarith
    have hone : (1:ℝ) ≤ 2 / (1 + t ^ 2) := (one_le_div h1t).mpr h2
    have h3 : (1:ℝ) / e ^ 4 ≤ (2 / e ^ 4) / (1 + t ^ 2) := by
      have hh : (1:ℝ) / e ^ 4 * 1 ≤ (1 / e ^ 4) * (2 / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
      rw [mul_one] at hh
      have heq : (1 / e ^ 4) * (2 / (1 + t ^ 2)) = (2 / e ^ 4) / (1 + t ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
      rwa [heq] at hh
    have h4 : (2 / e ^ 4) / (1 + t ^ 2) ≤ max (2 / e ^ 4) 4 / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right (le_max_left _ _) h1t.le
    linarith
  · have hgam_ge : |t| ≤ ‖gam β t‖ := Commons.Analysis.Integral.gam_norm_ge_abs β t
    have hpow : |t| ^ 4 ≤ ‖gam β t‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg t) hgam_ge 4
    have ht4 : |t| ^ 4 = t ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [ht4] at hpow
    have ht2 : 1 < t ^ 2 := by
      have h : (1:ℝ) < |t| ^ 2 := by nlinarith [abs_nonneg t]
      rwa [show |t| ^ 2 = t ^ 2 by rw [← abs_pow, abs_of_nonneg (by positivity)]] at h
    have ht4pos : 0 < t ^ 4 := by nlinarith [ht2]
    have hle : (1:ℝ) / ‖gam β t‖ ^ 4 ≤ 1 / t ^ 4 :=
      one_div_le_one_div_of_le ht4pos hpow
    have hsq : (1 + t ^ 2) ^ 2 ≤ 4 * t ^ 4 := by nlinarith [ht2]
    have hge : (1 + t ^ 2) ^ 2 / 4 ≤ t ^ 4 := by nlinarith [hsq]
    have hpos2 : 0 < (1 + t ^ 2) ^ 2 / 4 := by positivity
    have hle2 : (1:ℝ) / t ^ 4 ≤ 4 / (1 + t ^ 2) ^ 2 := by
      have hh := one_div_le_one_div_of_le hpos2 hge
      have heq : 1 / ((1 + t ^ 2) ^ 2 / 4) = 4 / (1 + t ^ 2) ^ 2 := by
        rw [one_div, inv_div]
      rwa [heq] at hh
    have h3 : (4:ℝ) / (1 + t ^ 2) ^ 2 ≤ 4 / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num)
      · positivity
      · nlinarith [sq_nonneg t]
    have h4 : (4:ℝ) / (1 + t ^ 2) ≤ max (2 / e ^ 4) 4 / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right (le_max_right _ _) h1t.le
    linarith

/-- Pointwise domination of the integrand by an explicit model function. -/
private lemma integrand_pointwise_le {β C₁ Cg : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hC1 : 0 < C₁)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hCg : ∀ t : ℝ, 1 / ‖gam β t‖ ^ 4 ≤ Cg / (1 + t ^ 2)) (t : ℝ) :
    ‖gamDot β t‖ / (‖riemannZeta (1 + gam β t)‖ * ‖riemannZeta (1 - gam β t)‖ * ‖gam β t‖ ^ 4)
        ≤ ((β / (2 * (Real.log 2) ^ 2) + 1) * C₁ ^ 2 * Cg)
            * ((Real.log (|t| + 2) + 1) ^ 2 / (1 + t ^ 2)) := by
  set L : ℝ := Real.log (|t| + 2) + 1 with hL
  set Kdot : ℝ := β / (2 * (Real.log 2) ^ 2) + 1 with hKdot
  have hKdotpos : 0 < Kdot := by
    rw [hKdot]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hLnn : 0 ≤ L := by
    rw [hL]
    have h : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by have := abs_nonneg t; linarith)
    linarith
  have hN : ‖gamDot β t‖ ≤ Kdot := by
    rw [hKdot]; exact Commons.Analysis.Integral.gamDot_norm_le hβ t
  have hA : (‖riemannZeta (1 + gam β t)‖)⁻¹ ≤ C₁ * L := by
    have h := inv_zeta_gam_le hβ hinvb t
    rw [norm_inv] at h
    rw [hL]; exact h
  have hB : (‖riemannZeta (1 - gam β t)‖)⁻¹ ≤ C₁ * L := by
    have h := inv_zeta_neg_gam_le hβ hβ10 hinvb t
    rw [norm_inv] at h
    rw [hL]; exact h
  have hC : (‖gam β t‖ ^ 4)⁻¹ ≤ Cg / (1 + t ^ 2) := by
    have h := hCg t; rwa [one_div] at h
  have hdecomp : ‖gamDot β t‖
        / (‖riemannZeta (1 + gam β t)‖ * ‖riemannZeta (1 - gam β t)‖ * ‖gam β t‖ ^ 4)
      = ‖gamDot β t‖ * (‖riemannZeta (1 + gam β t)‖)⁻¹
        * (‖riemannZeta (1 - gam β t)‖)⁻¹ * (‖gam β t‖ ^ 4)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [hdecomp]
  have hCL : 0 ≤ C₁ * L := mul_nonneg hC1.le hLnn
  have step1 : ‖gamDot β t‖ * (‖riemannZeta (1 + gam β t)‖)⁻¹ ≤ Kdot * (C₁ * L) :=
    mul_le_mul hN hA (by positivity) hKdotpos.le
  have step2 : ‖gamDot β t‖ * (‖riemannZeta (1 + gam β t)‖)⁻¹
        * (‖riemannZeta (1 - gam β t)‖)⁻¹ ≤ (Kdot * (C₁ * L)) * (C₁ * L) :=
    mul_le_mul step1 hB (by positivity) (mul_nonneg hKdotpos.le hCL)
  have step3 : ‖gamDot β t‖ * (‖riemannZeta (1 + gam β t)‖)⁻¹
        * (‖riemannZeta (1 - gam β t)‖)⁻¹ * (‖gam β t‖ ^ 4)⁻¹
      ≤ (Kdot * (C₁ * L)) * (C₁ * L) * (Cg / (1 + t ^ 2)) :=
    mul_le_mul step2 hC (by positivity) (mul_nonneg (mul_nonneg hKdotpos.le hCL) hCL)
  refine step3.trans (le_of_eq ?_)
  rw [hKdot, hL]; ring

theorem gam0_zeta_quartic_integral_le {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (C₁ : ℝ) (hC1 : 0 < C₁)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1)) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t : ℝ, ‖Commons.Analysis.Complex.gamDot β t‖
          / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
              * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
              * ‖Commons.Analysis.Complex.gam β t‖ ^ 4)) ≤ C := by
  obtain ⟨Cg, hCgpos, hCgb⟩ := inv_norm_gam_pow4_le hβ
  set Kdot : ℝ := β / (2 * (Real.log 2) ^ 2) + 1 with hKdot
  have hKdotpos : 0 < Kdot := by
    rw [hKdot]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  set D : ℝ := Kdot * C₁ ^ 2 * Cg with hDdef
  set G : ℝ → ℝ := fun t => (Real.log (|t| + 2) + 1) ^ 2 / (1 + t ^ 2) with hGdef
  have hGint : Integrable G volume := by
    rw [hGdef]
    simpa using Commons.Analysis.Integral.integrable_log_sq_lorentz 1 0 one_pos
  have hgint : Integrable (fun t => D * G t) volume := hGint.const_mul D
  set F : ℝ → ℝ := fun t => ‖Commons.Analysis.Complex.gamDot β t‖
      / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β t)‖
          * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β t)‖
          * ‖Commons.Analysis.Complex.gam β t‖ ^ 4) with hFdef
  have hpt : ∀ t : ℝ, ‖F t‖ ≤ D * G t := by
    intro t
    have hFnn : 0 ≤ F t := by rw [hFdef]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn, hFdef, hDdef, hGdef, hKdot]
    exact integrand_pointwise_le hβ hβ10 hC1 hinvb hCgb t
  have h := MeasureTheory.norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hInt : (∫ t, D * G t) = D * ∫ t, G t := MeasureTheory.integral_const_mul D G
  refine ⟨max 1 (D * ∫ t, G t), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  change (∫ t, F t) ≤ max 1 (D * ∫ t, G t)
  calc (∫ t, F t) ≤ |∫ t, F t| := le_abs_self _
    _ = ‖∫ t, F t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, D * G t := h
    _ = D * ∫ t, G t := hInt
    _ ≤ max 1 (D * ∫ t, G t) := le_max_right _ _

end

end Commons.NumberTheory.Zeta
