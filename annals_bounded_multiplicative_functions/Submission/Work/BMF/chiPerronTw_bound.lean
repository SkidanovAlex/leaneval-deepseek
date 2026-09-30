import Mathlib
import Submission.Work.BMF.perron_twist_core
import Submission.Work.BMF.integral_inv_sqrt_sq_add_sq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bound for the twisted truncated Perron integral `chiPerronTw`

If `L(·, χ)` is zero-free on the rectangle `[σ₁, 1 + 1/log x] × [-T, T]` shifted by `iu`, and
its logarithmic derivative is bounded by `B` there, then the twisted truncated Perron integral is
bounded by

`B · x^{1+1/log x} / T · (1 + 1/log x - σ₁) + B · x^{σ₁} · (3 + 3 log (2 + T/σ₁))`.

The proof shifts the contour (`chiPerronTw_rect`) and bounds the horizontal edges by
`B x^σ/T` and the vertical edge by the elementary integral
`∫_{-T}^{T} dt/√(σ₁²+t²) ≤ 2 + 2 log(2 + T/σ₁)`.
-/

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped Interval Topology


/-- Pointwise norm bound for the twisted Perron integrand on the strip. -/
lemma chiTwGTw_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u x T σ₁ c B : ℝ} (hx : 1 < x)
    (hB : ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ c → |t - u| ≤ T →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B)
    {w : ℂ} (hre : w.re ∈ Set.Icc σ₁ c) (him : |w.im| ≤ T) :
    ‖chiGTw χ u x w‖ ≤ B * x ^ w.re / ‖w‖ := by
  have hxpos : 0 < x := by linarith
  have harg : ((w.re : ℂ) + ((w.im + u : ℝ) : ℂ) * Complex.I) = w + (u : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hBw : ‖logDeriv (DirichletCharacter.LFunction χ) (w + (u : ℂ) * Complex.I)‖ ≤ B := by
    rw [← harg]
    exact hB w.re (w.im + u) hre (by rw [add_sub_cancel_right]; exact him)
  have hchidef : chiGTw χ u x w =
      -(logDeriv (DirichletCharacter.LFunction χ) (w + (u : ℂ) * Complex.I)) *
        (x : ℂ) ^ w / w := by
    rw [chiGTw, logDeriv_apply]; ring
  rw [hchidef, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hBw (Real.rpow_nonneg hxpos.le _)) (norm_nonneg w)

/-- Pointwise bound on a horizontal edge `Re w = v`, `Im w = T`. -/
lemma chiTwGTw_horiz_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u x T σ₁ c B : ℝ} (hx : 1 < x) (hT : 0 < T)
    (hB : ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ c → |t - u| ≤ T →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B)
    (hB0 : 0 ≤ B) {v : ℝ} (hv : v ∈ Set.Icc σ₁ c) :
    ‖chiGTw χ u x ((v : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B * x ^ c / T := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxv : x ^ v ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx.le hv.2
  have hw : ((v : ℂ) + (T : ℂ) * Complex.I).re = v := by simp
  have hwi : ((v : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
  have h1 := chiTwGTw_norm_le χ hx hB (w := (v : ℂ) + (T : ℂ) * Complex.I)
      (by rw [hw]; exact hv) (by rw [hwi]; exact le_of_eq (abs_of_pos hT))
  rw [hw] at h1
  refine le_trans h1 ?_
  rw [Complex.norm_add_mul_I, div_eq_mul_inv, div_eq_mul_inv]
  have hxT : T ≤ Real.sqrt (v ^ 2 + T ^ 2) := by
    rw [Real.le_sqrt (le_of_lt hT) (by positivity)]
    nlinarith [sq_nonneg v]
  have hinv : (Real.sqrt (v ^ 2 + T ^ 2))⁻¹ ≤ T⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hT hxT
  exact mul_le_mul (mul_le_mul_of_nonneg_left hxv hB0) hinv (by positivity)
    (mul_nonneg hB0 (Real.rpow_nonneg hx0 c))

/-- Pointwise bound on the vertical edge `Re w = σ₁`. -/
lemma chiTwGTw_vert_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u x T σ₁ c B : ℝ} (hx : 1 < x) (hT : 0 < T)
    (hB : ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ c → |t - u| ≤ T →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B)
    (hσ₁c : σ₁ ∈ Set.Icc σ₁ c) {t : ℝ} (ht : |t| ≤ T) :
    ‖chiGTw χ u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      B * x ^ σ₁ * (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹ := by
  have hw : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).re = σ₁ := by simp
  have hwi : ((σ₁ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have h1 := chiTwGTw_norm_le χ hx hB (w := (σ₁ : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hw]; exact hσ₁c) (by rw [hwi]; exact ht)
  rw [hw, Complex.norm_add_mul_I, div_eq_mul_inv] at h1
  exact h1

/-- `‖1/(2πi)‖ = 1/(2π)`. -/
lemma chiTw_norm_one_div_two_pi_I :
    ‖((1 / (2 * Real.pi * Complex.I)) : ℂ)‖ = 1 / (2 * Real.pi) := by
  rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2, hp]

/-- `‖1/(2π)‖ = 1/(2π)`. -/
lemma chiTw_norm_one_div_two_pi :
    ‖((1 / (2 * Real.pi)) : ℂ)‖ = 1 / (2 * Real.pi) := by
  rw [norm_div, norm_one, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2, hp]

theorem chiPerronTw_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {u x T σ₁ B : ℝ} (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁)
    (hσ₁lt : σ₁ < 1 + 1 / Real.log x)
    (hL0 : ∀ s : ℂ, s.re ∈ Set.Icc σ₁ (1 + 1 / Real.log x) → |s.im - u| ≤ T →
      DirichletCharacter.LFunction χ s ≠ 0)
    (hB : ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ (1 + 1 / Real.log x) → |t - u| ≤ T →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B) :
    ‖chiPerronTw χ u x T‖ ≤
      B * x ^ (1 + 1 / Real.log x) / T * (1 + 1 / Real.log x - σ₁) +
      B * x ^ σ₁ * (3 + 3 * Real.log (2 + T / σ₁)) := by
  have hrect := chiPerronTw_rect χ hχ hx hT hσ₁ hσ₁lt hL0
  set c : ℝ := 1 + 1 / Real.log x with hc
  set L : ℝ := Real.log (2 + T / σ₁) with hL
  have hσ₁c : σ₁ ≤ c := le_of_lt hσ₁lt
  have hcpos : 0 < c := lt_trans hσ₁ hσ₁lt
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg (by have : 0 < T / σ₁ := div_pos hT hσ₁; linarith)
  have hB0 : 0 ≤ B := by
    have h := hB σ₁ u (Set.mem_Icc.mpr ⟨le_refl σ₁, hσ₁c⟩)
      (by rw [sub_self, abs_zero]; exact hT.le)
    exact le_trans (norm_nonneg _) h
  rw [hrect]
  set AP : ℂ := ∫ v in σ₁..c, chiGTw χ u x ((v : ℂ) + (T : ℂ) * Complex.I) with hAP
  set AM : ℂ := ∫ v in σ₁..c, chiGTw χ u x ((v : ℂ) - (T : ℂ) * Complex.I) with hAM
  set VV : ℂ := ∫ t in (-T)..T, chiGTw χ u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I) with hVV
  have hAPb : ‖AP‖ ≤ B * x ^ c / T * (c - σ₁) := by
    rw [hAP]
    have hpt : ∀ v ∈ Set.uIoc σ₁ c,
        ‖chiGTw χ u x ((v : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B * x ^ c / T := by
      intro v hv
      rw [Set.uIoc_of_le hσ₁c] at hv
      exact chiTwGTw_horiz_le χ hx hT hB hB0 ⟨le_of_lt hv.1, hv.2⟩
    calc ‖∫ v in σ₁..c, chiGTw χ u x ((v : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ (B * x ^ c / T) * |c - σ₁| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = B * x ^ c / T * (c - σ₁) := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - σ₁)]
  have hAMb : ‖AM‖ ≤ B * x ^ c / T * (c - σ₁) := by
    rw [hAM]
    have hpt : ∀ v ∈ Set.uIoc σ₁ c,
        ‖chiGTw χ u x ((v : ℂ) - (T : ℂ) * Complex.I)‖ ≤ B * x ^ c / T := by
      intro v hv
      rw [Set.uIoc_of_le hσ₁c] at hv
      have hvc : v ∈ Set.Icc σ₁ c := ⟨le_of_lt hv.1, hv.2⟩
      have hre : ((v : ℂ) - (T : ℂ) * Complex.I).re = v := by simp
      have him : ((v : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
      have h1 := chiTwGTw_norm_le χ hx hB (w := (v : ℂ) - (T : ℂ) * Complex.I)
          (by rw [hre]; exact hvc)
          (by rw [him, abs_neg]; exact le_of_eq (abs_of_pos hT))
      rw [hre] at h1
      refine le_trans h1 ?_
      have hxv : x ^ v ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx.le hv.2
      rw [show ‖(v : ℂ) - (T : ℂ) * Complex.I‖ = Real.sqrt (v ^ 2 + T ^ 2) by
            rw [show (v : ℂ) - (T : ℂ) * Complex.I =
                (v : ℂ) + ((-T : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_add_mul_I]
            congr 1; ring]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hxT : T ≤ Real.sqrt (v ^ 2 + T ^ 2) := by
        rw [Real.le_sqrt (le_of_lt hT) (by positivity)]
        nlinarith [sq_nonneg v]
      have hinv : (Real.sqrt (v ^ 2 + T ^ 2))⁻¹ ≤ T⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hT hxT
      exact mul_le_mul (mul_le_mul_of_nonneg_left hxv hB0) hinv (by positivity)
        (mul_nonneg hB0 (Real.rpow_nonneg hx0 c))
    calc ‖∫ v in σ₁..c, chiGTw χ u x ((v : ℂ) - (T : ℂ) * Complex.I)‖
        ≤ (B * x ^ c / T) * |c - σ₁| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = B * x ^ c / T * (c - σ₁) := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - σ₁)]
  have hVVb : ‖VV‖ ≤ B * x ^ σ₁ * (2 + 2 * L) := by
    rw [hVV]
    have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc (-T) T →
        ‖chiGTw χ u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          B * x ^ σ₁ * (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹ := by
      refine Filter.Eventually.of_forall fun t ht => ?_
      refine chiTwGTw_vert_le χ hx hT hB (Set.mem_Icc.mpr ⟨le_refl σ₁, hσ₁c⟩) ?_
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    have hint : IntervalIntegrable
        (fun t : ℝ => B * x ^ σ₁ * (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹) volume (-T) T := by
      apply Continuous.intervalIntegrable
      apply Continuous.mul continuous_const
      apply Continuous.inv₀ (Real.continuous_sqrt.comp (by continuity))
      intro t; exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (show (-T:ℝ) ≤ T by linarith) hpt hint
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 : (∫ t in (-T)..T, (Real.sqrt (σ₁ ^ 2 + t ^ 2))⁻¹) ≤ 2 + 2 * L := by
      rw [hL]; exact integral_inv_sqrt_sq_add_sq_le hσ₁ hT
    exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hB0 (Real.rpow_nonneg hx0 σ₁))
  have hA : ‖(1 / (2 * Real.pi * Complex.I)) * (AP - AM)‖ ≤ B * x ^ c / T * (c - σ₁) := by
    rw [norm_mul, chiTw_norm_one_div_two_pi_I]
    have hsub : ‖AP - AM‖ ≤ 2 * (B * x ^ c / T * (c - σ₁)) := by
      refine le_trans (norm_sub_le AP AM) ?_
      rw [two_mul]
      exact add_le_add hAPb hAMb
    have hX : 0 ≤ B * x ^ c / T * (c - σ₁) := by
      have h1 : 0 ≤ B * x ^ c := mul_nonneg hB0 (Real.rpow_nonneg hx0 c)
      exact mul_nonneg (div_nonneg h1 hT.le) (by linarith)
    calc (1 / (2 * Real.pi)) * ‖AP - AM‖
        ≤ (1 / (2 * Real.pi)) * (2 * (B * x ^ c / T * (c - σ₁))) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = B * x ^ c / T * (c - σ₁) / Real.pi := by field_simp
      _ ≤ B * x ^ c / T * (c - σ₁) := by
          exact div_le_self hX (by linarith [Real.pi_gt_three])
  have hV : ‖(1 / (2 * Real.pi)) * VV‖ ≤ B * x ^ σ₁ * (3 + 3 * L) := by
    rw [norm_mul, chiTw_norm_one_div_two_pi]
    have hP : 0 ≤ B * x ^ σ₁ := mul_nonneg hB0 (Real.rpow_nonneg hx0 σ₁)
    calc (1 / (2 * Real.pi)) * ‖VV‖ ≤ (1 / (2 * Real.pi)) * (B * x ^ σ₁ * (2 + 2 * L)) :=
          mul_le_mul_of_nonneg_left hVVb (by positivity)
      _ = B * x ^ σ₁ * ((1 / (2 * Real.pi)) * (2 + 2 * L)) := by ring
      _ ≤ B * x ^ σ₁ * (3 + 3 * L) := by
          apply mul_le_mul_of_nonneg_left _ hP
          have h1 : (1 / (2 * Real.pi)) * (2 + 2 * L) = (1 + L) / Real.pi := by field_simp
          rw [h1]
          have h2 : (1 + L) / Real.pi ≤ 1 + L := by
            rw [div_le_iff₀ Real.pi_pos]
            nlinarith [hLnn, Real.pi_gt_three]
          linarith
  calc ‖(1 / (2 * Real.pi * Complex.I)) * (AP - AM) + (1 / (2 * Real.pi)) * VV‖
      ≤ ‖(1 / (2 * Real.pi * Complex.I)) * (AP - AM)‖ + ‖(1 / (2 * Real.pi)) * VV‖ :=
        norm_add_le _ _
    _ ≤ B * x ^ c / T * (c - σ₁) + B * x ^ σ₁ * (3 + 3 * L) := add_le_add hA hV

end Work.BMF
