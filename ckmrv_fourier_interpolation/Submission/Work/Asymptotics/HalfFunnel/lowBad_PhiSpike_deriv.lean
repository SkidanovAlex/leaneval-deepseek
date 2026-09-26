/-
Fourier interpolation (CKMRV), low-strip bad-line spike.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.Asymptotics.HalfFunnel.spike_inv_integral_bound

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped Interval

namespace Work.Asymptotics.HalfFunnel

open Work.Kernels

/-- Mean-value bound valid for `0 ≤ a`. -/
private lemma spike_exp_sub_le_nonneg {a y ρ u : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (hρy : ρ < y)
    (hu : u ∈ Set.Icc (-ρ) ρ) :
    |Real.exp (-(a * (y + u))) - Real.exp (-(a * y))|
      ≤ a * Real.exp (-(a * (y - ρ))) * |u| := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp
  · exact spike_exp_sub_le h hρ hρy hu

/-- Base case (`m = 0`) of the decaying model integral. -/
private lemma spike_base_decay {ρ Y : ℝ} (hρ : 0 < ρ) (hρY : ρ < Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y a ε : ℝ), ρ < y → y ≤ Y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹‖
        ≤ C * (1 + a) * Real.exp (-(a * (y - ρ))) := by
  refine ⟨2 * ρ + Real.pi, by positivity, ?_⟩
  intro y a ε hy hyY ha hε hε4
  have hc : 0 < y - ρ := by linarith
  have hle : -ρ ≤ ρ := by linarith
  have hsqD : ∀ u : ℝ, u ^ 2 + ε ^ 2 ≠ 0 := by
    intro u; nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
  have hEpos : 0 < Real.exp (-(a * (y - ρ))) := Real.exp_pos _
  have hpt : ∀ u : ℝ,
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹
      = ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
        + (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
        - (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I := by
    intro u
    have hDc : ((u ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqD u
    rw [spike_exp_neg_mul_ofReal, spike_inv_add_mul_I hε]
    push_cast
    field_simp
    ring
  have hInt0 : (∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) = 0 := by
    have hcongr : (∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
        = ∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * (u / (u ^ 2 + ε ^ 2)) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _
      rw [Complex.ofReal_inj]
      ring
    rw [hcongr, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
      spike_odd_integral, mul_zero, Complex.ofReal_zero]
  have hi0 : IntervalIntegrable
      (fun u : ℝ => ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) volume (-ρ) ρ := by
    have hr : Continuous (fun u : ℝ => Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2)) := by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · exact hsqD
    exact (Complex.continuous_ofReal.comp hr).intervalIntegrable (-ρ) ρ
  have hi1 : IntervalIntegrable
      (fun u : ℝ =>
        (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
      volume (-ρ) ρ := by
    have hr : Continuous
        (fun u : ℝ => (Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2)) := by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · exact hsqD
    exact (Complex.continuous_ofReal.comp hr).intervalIntegrable (-ρ) ρ
  have hi2 : IntervalIntegrable
      (fun u : ℝ =>
        (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)
      volume (-ρ) ρ := by
    have hr : Continuous (fun u : ℝ => (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε) := by
      apply Continuous.mul
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · exact hsqD
      · fun_prop
    have hc2 : Continuous
        (fun u : ℝ => (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ)
          * Complex.I) :=
      (Complex.continuous_ofReal.comp hr).mul continuous_const
    exact hc2.intervalIntegrable (-ρ) ρ
  have hInt1 : ‖∫ u in (-ρ)..ρ,
      (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
      ≤ a * Real.exp (-(a * (y - ρ))) * (2 * ρ) := by
    have hpt_bound : ∀ u ∈ Set.uIoc (-ρ) ρ,
        ‖(((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
          ≤ a * Real.exp (-(a * (y - ρ))) := by
      intro u hu
      have hu' : u ∈ Set.Icc (-ρ) ρ := by
        rw [Set.uIoc_of_le hle] at hu
        exact ⟨le_of_lt hu.1, hu.2⟩
      have hDpos : 0 < u ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
      have hgu := spike_exp_sub_le_nonneg ha hρ hy hu'
      have hkey : ‖(((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u
          / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
          = |Real.exp (-(a * (y + u))) - Real.exp (-(a * y))| * |u| / (u ^ 2 + ε ^ 2) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hDpos]
      rw [hkey]
      calc |Real.exp (-(a * (y + u))) - Real.exp (-(a * y))| * |u| / (u ^ 2 + ε ^ 2)
          ≤ (a * Real.exp (-(a * (y - ρ))) * |u|) * |u| / (u ^ 2 + ε ^ 2) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hgu (abs_nonneg u)) hDpos.le
        _ = a * Real.exp (-(a * (y - ρ))) * (|u| ^ 2 / (u ^ 2 + ε ^ 2)) := by ring
        _ ≤ a * Real.exp (-(a * (y - ρ))) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one hDpos]
            nlinarith [sq_nonneg ε, sq_abs u]
        _ = a * Real.exp (-(a * (y - ρ))) := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -ρ) (b := ρ)
      (f := fun u : ℝ =>
        (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
      (C := a * Real.exp (-(a * (y - ρ)))) hpt_bound
    rw [show ρ - (-ρ) = 2 * ρ by ring, abs_of_pos (by linarith : (0:ℝ) < 2 * ρ)] at h
    exact h
  have hInt2 : ‖∫ u in (-ρ)..ρ,
      (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖
      ≤ Real.pi * Real.exp (-(a * (y - ρ))) := by
    have hcont1 : Continuous (fun u : ℝ => Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) := by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · exact hsqD
    have hcont2 : Continuous (fun u : ℝ => (u ^ 2 + ε ^ 2)⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · exact hsqD
    have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := -ρ) (b := ρ)
      (f := fun u : ℝ => (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ)
        * Complex.I) hle
    have h2 : (∫ u in (-ρ)..ρ,
          ‖(((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖)
        = |ε| * ∫ u in (-ρ)..ρ, (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      have hDpos : 0 < u ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg u, sq_pos_of_ne_zero hε]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hDpos]
      ring
    have h3 : (∫ u in (-ρ)..ρ, (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)))
        ≤ Real.exp (-(a * (y - ρ))) * ∫ u in (-ρ)..ρ, (u ^ 2 + ε ^ 2)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hle
        (hcont1.intervalIntegrable _ _) (hcont2.const_mul _ |>.intervalIntegrable _ _)
      intro u hu
      have hgu : Real.exp (-(a * (y + u))) ≤ Real.exp (-(a * (y - ρ))) := by
        rw [Real.exp_le_exp]
        nlinarith [hu.1, ha]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hgu (by positivity)
    calc ‖∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖
        ≤ ∫ u in (-ρ)..ρ,
            ‖(((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖ := h1
      _ = |ε| * ∫ u in (-ρ)..ρ, (Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) := h2
      _ ≤ |ε| * (Real.exp (-(a * (y - ρ))) * ∫ u in (-ρ)..ρ, (u ^ 2 + ε ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg ε)
      _ = Real.exp (-(a * (y - ρ))) * (|ε| * ∫ u in (-ρ)..ρ, (u ^ 2 + ε ^ 2)⁻¹) := by ring
      _ ≤ Real.exp (-(a * (y - ρ))) * (|ε| * (Real.pi / |ε|)) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            exact mul_le_mul_of_nonneg_left (spike_inv_sq_integral_le hε) (abs_nonneg ε)
      _ = Real.pi * Real.exp (-(a * (y - ρ))) := by
            rw [mul_div_cancel₀ _ (abs_ne_zero.mpr hε)]; ring
  have e1 : (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))
        * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹)
      = ∫ u in (-ρ)..ρ, (((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
          + (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
          - (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact hpt u
  have e2 : (∫ u in (-ρ)..ρ, (((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
          + (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)
          - ((((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)))
      = (∫ u in (-ρ)..ρ, ((Real.exp (-(a * y)) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
        + (∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
        - (∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_sub (hi0.add hi1) hi2, intervalIntegral.integral_add hi0 hi1]
  rw [e1, e2, hInt0, zero_add]
  calc ‖(∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ))
          - (∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I)‖
      ≤ ‖∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) - Real.exp (-(a * y))) * u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)‖
        + ‖∫ u in (-ρ)..ρ,
            (((Real.exp (-(a * (y + u))) / (u ^ 2 + ε ^ 2)) * ε : ℝ) : ℂ) * Complex.I‖ :=
        norm_sub_le _ _
    _ ≤ a * Real.exp (-(a * (y - ρ))) * (2 * ρ) + Real.pi * Real.exp (-(a * (y - ρ))) :=
        add_le_add hInt1 hInt2
    _ = (2 * ρ * a + Real.pi) * Real.exp (-(a * (y - ρ))) := by ring
    _ ≤ (2 * ρ + Real.pi) * (1 + a) * Real.exp (-(a * (y - ρ))) := by
        apply mul_le_mul_of_nonneg_right _ hEpos.le
        nlinarith [Real.pi_pos, hρ.le, ha]

/-- Induction step for the decaying model integral. -/
private lemma spike_step {ρ Y : ℝ} (hρ : 0 < ρ) (hρY : ρ < Y) (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (y a ε : ℝ), ρ < y → y ≤ Y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m‖
        ≤ C * (1 + a) * Real.exp (-(a * (y - ρ)))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (y a ε : ℝ), ρ < y → y ≤ Y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ (m + 1)‖
        ≤ C' * (1 + a) * Real.exp (-(a * (y - ρ))) := by
  have hYpos : 0 < Y := lt_trans hρ hρY
  refine ⟨2 * ρ * (Y + ρ) ^ m + (Y + 1 / 4) * C, by positivity, ?_⟩
  intro y a ε hy hyY ha hε hε4
  have hEpos : 0 < Real.exp (-(a * (y - ρ))) := Real.exp_pos _
  have hne : ∀ u : ℝ, ((u : ℂ) + (ε : ℂ) * Complex.I) ≠ 0 := by
    intro u h
    have := congrArg Complex.im h
    simp at this
    exact hε this
  have key : ∀ u : ℝ, ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ (m + 1)
      = ((y : ℂ) + (u : ℂ)) ^ m +
        ((y : ℂ) - (ε : ℂ) * Complex.I) *
          (((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m) := by
    intro u
    have hA : ((u : ℂ) + (ε : ℂ) * Complex.I) ≠ 0 := hne u
    have hthis : ((u : ℂ) + (ε : ℂ) * Complex.I) *
          (((y : ℂ) - (ε : ℂ) * Complex.I) *
            (((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m))
        = ((y : ℂ) - (ε : ℂ) * Complex.I) * ((y : ℂ) + (u : ℂ)) ^ m := by
      calc ((u : ℂ) + (ε : ℂ) * Complex.I) *
            (((y : ℂ) - (ε : ℂ) * Complex.I) *
              (((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m))
          = (((u : ℂ) + (ε : ℂ) * Complex.I) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹) *
              (((y : ℂ) - (ε : ℂ) * Complex.I) * ((y : ℂ) + (u : ℂ)) ^ m) := by ring
        _ = ((y : ℂ) - (ε : ℂ) * Complex.I) * ((y : ℂ) + (u : ℂ)) ^ m := by
            rw [mul_inv_cancel₀ hA, one_mul]
    have h2 : ((u : ℂ) + (ε : ℂ) * Complex.I) *
          (((y : ℂ) + (u : ℂ)) ^ m + ((y : ℂ) - (ε : ℂ) * Complex.I) *
            (((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m))
        = ((y : ℂ) + (u : ℂ)) ^ (m + 1) := by
      rw [mul_add, hthis, ← add_mul, show ((u : ℂ) + (ε : ℂ) * Complex.I) +
          ((y : ℂ) - (ε : ℂ) * Complex.I) = (y : ℂ) + (u : ℂ) by ring, pow_succ]
      ring
    rw [← h2, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
  have hstep : ∀ u : ℝ,
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
          ((y : ℂ) + (u : ℂ)) ^ (m + 1)
      = Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m
        + ((y : ℂ) - (ε : ℂ) * Complex.I) *
          (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
            ((y : ℂ) + (u : ℂ)) ^ m) := by
    intro u
    rw [mul_assoc, key u]
    ring
  have hcont_a : Continuous (fun u : ℝ =>
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m) := by fun_prop
  have hcont_b : Continuous (fun u : ℝ =>
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
        ((y : ℂ) + (u : ℂ)) ^ m) := by
    apply Continuous.mul
    · apply Continuous.mul
      · fun_prop
      · exact Continuous.inv₀ (by fun_prop) (fun u => hne u)
    · fun_prop
  have hia : IntervalIntegrable (fun u : ℝ =>
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m) volume (-ρ) ρ :=
    hcont_a.intervalIntegrable _ _
  have hib : IntervalIntegrable (fun u : ℝ =>
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
        ((y : ℂ) + (u : ℂ)) ^ m) volume (-ρ) ρ := hcont_b.intervalIntegrable _ _
  have hcongr : (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
        ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ (m + 1))
      = ∫ u in (-ρ)..ρ, (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m
          + ((y : ℂ) - (ε : ℂ) * Complex.I) *
            (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ *
              ((y : ℂ) + (u : ℂ)) ^ m)) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact hstep u
  have h1 : ‖∫ u in (-ρ)..ρ,
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m‖
      ≤ (Y + ρ) ^ m * (2 * ρ) * Real.exp (-(a * (y - ρ))) := by
    have hb : ∀ u ∈ Set.uIoc (-ρ) ρ,
        ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m‖
          ≤ (Y + ρ) ^ m * Real.exp (-(a * (y - ρ))) := by
      intro u hu
      rw [Set.uIoc_of_le (by linarith : -ρ ≤ ρ)] at hu
      have huI : -ρ ≤ u ∧ u ≤ ρ := ⟨le_of_lt hu.1, hu.2⟩
      have hnormE : ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))‖
          = Real.exp (-(a * (y + u))) := by
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re, Complex.add_re, Complex.add_im]
      have hnormP : ‖((y : ℂ) + (u : ℂ)) ^ m‖ ≤ (Y + ρ) ^ m := by
        rw [norm_pow, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
        apply pow_le_pow_left₀ (abs_nonneg _)
        rw [abs_le]; constructor <;> linarith
      have hexp : Real.exp (-(a * (y + u))) ≤ Real.exp (-(a * (y - ρ))) := by
        rw [Real.exp_le_exp]; nlinarith [huI.1, ha]
      calc ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m‖
          = ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))‖ * ‖((y : ℂ) + (u : ℂ)) ^ m‖ :=
            norm_mul _ _
        _ = Real.exp (-(a * (y + u))) * ‖((y : ℂ) + (u : ℂ)) ^ m‖ := by rw [hnormE]
        _ ≤ Real.exp (-(a * (y - ρ))) * (Y + ρ) ^ m :=
            mul_le_mul hexp hnormP (norm_nonneg _) (Real.exp_pos _).le
        _ = (Y + ρ) ^ m * Real.exp (-(a * (y - ρ))) := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -ρ) (b := ρ)
      (f := fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m)
      (C := (Y + ρ) ^ m * Real.exp (-(a * (y - ρ)))) hb
    rw [show ρ - (-ρ) = 2 * ρ by ring, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ρ)] at h
    calc ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m‖
        ≤ (Y + ρ) ^ m * Real.exp (-(a * (y - ρ))) * (2 * ρ) := h
      _ = (Y + ρ) ^ m * (2 * ρ) * Real.exp (-(a * (y - ρ))) := by ring
  have h2 : ‖((y : ℂ) - (ε : ℂ) * Complex.I) *
        (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m)‖
      ≤ (Y + 1 / 4) * (C * (1 + a) * Real.exp (-(a * (y - ρ)))) := by
    rw [norm_mul]
    have hle : ‖(y : ℂ) - (ε : ℂ) * Complex.I‖ ≤ Y + 1 / 4 := by
      calc ‖(y : ℂ) - (ε : ℂ) * Complex.I‖ ≤ ‖(y : ℂ)‖ + ‖(ε : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ = y + |ε| := by
            rw [norm_mul, Complex.norm_I, mul_one]
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (lt_trans hρ hy))]
        _ ≤ Y + 1 / 4 := by linarith [abs_le.mpr ⟨by linarith [abs_nonneg ε], hε4⟩]
    exact mul_le_mul hle (hbound y a ε hy hyY ha hε hε4) (norm_nonneg _) (by positivity)
  rw [hcongr, intervalIntegral.integral_add hia (hib.const_mul _),
    intervalIntegral.integral_const_mul]
  calc ‖(∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((y : ℂ) + (u : ℂ)) ^ m)
        + ((y : ℂ) - (ε : ℂ) * Complex.I) *
          (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
            ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m)‖
      ≤ ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
            ((y : ℂ) + (u : ℂ)) ^ m‖
        + ‖((y : ℂ) - (ε : ℂ) * Complex.I) *
          (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
            ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m)‖ := norm_add_le _ _
    _ ≤ (Y + ρ) ^ m * (2 * ρ) * Real.exp (-(a * (y - ρ)))
        + (Y + 1 / 4) * (C * (1 + a) * Real.exp (-(a * (y - ρ)))) := add_le_add h1 h2
    _ = (2 * ρ * (Y + ρ) ^ m + (Y + 1 / 4) * C * (1 + a)) * Real.exp (-(a * (y - ρ))) := by ring
    _ ≤ (2 * ρ * (Y + ρ) ^ m + (Y + 1 / 4) * C) * (1 + a) * Real.exp (-(a * (y - ρ))) := by
        apply mul_le_mul_of_nonneg_right _ hEpos.le
        have hkey : (0:ℝ) ≤ (2 * ρ * (Y + ρ) ^ m) * a :=
          mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) m)) ha
        nlinarith [hkey]

/-- **Decaying model integral.** -/
private theorem spike_model_integral_decay (m : ℕ) {ρ Y : ℝ} (hρ : 0 < ρ) (hρY : ρ < Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y a ε : ℝ), ρ < y → y ≤ Y → 0 ≤ a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((y : ℂ) + (u : ℂ)) ^ m‖
        ≤ C * (1 + a) * Real.exp (-(a * (y - ρ))) := by
  induction m with
  | zero =>
      obtain ⟨C, hC, hb⟩ := spike_base_decay hρ hρY
      exact ⟨C, hC, fun y a ε hy hyY ha hε hε4 => by
        simpa [pow_zero] using hb y a ε hy hyY ha hε hε4⟩
  | succ m ih =>
      obtain ⟨C, hC, hb⟩ := ih
      exact spike_step hρ hρY m C hC hb



def spikeKf (C : ℂ) (s y : ℝ) (j : ℕ) (x : ℝ) (u : ℝ) : ℂ :=
  C * ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹ * (((-(Real.pi * (y + u)) : ℝ)) : ℂ) ^ j *
    Complex.exp ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ))

lemma karg (y x u : ℝ) :
    (((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ) = -(↑Real.pi * ↑x * (↑y + ↑u)) := by
  push_cast; ring

lemma continuous_spikeKf (C : ℂ) (s y : ℝ) (hs : s ≠ 0) (j : ℕ) (x : ℝ) :
    Continuous (fun u : ℝ => spikeKf C s y j x u) := by
  have hbase : Continuous (fun u : ℝ => ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun u h => by
      have h1 := congrArg Complex.re h
      simp at h1
      exact hs h1)
  have hc : Continuous (fun u : ℝ => (((-(Real.pi * (y + u)) : ℝ)) : ℂ) ^ j) := by fun_prop
  have hexp : Continuous (fun u : ℝ =>
      Complex.exp ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ))) := by fun_prop
  exact ((continuous_const.mul hbase).mul hc).mul hexp

lemma hasDerivAt_spikeKf (C : ℂ) (s y : ℝ) (hs : s ≠ 0) (j : ℕ) (x u : ℝ) :
    HasDerivAt (fun x : ℝ => spikeKf C s y j x u) (spikeKf C s y (j + 1) x u) x := by
  have hbase : HasDerivAt (fun x : ℝ => Complex.exp ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ)))
      ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) *
        Complex.exp ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ))) x := by
    have hmul : HasDerivAt (fun x : ℝ => (((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ))
        (((-(Real.pi * (y + u)) : ℝ)) : ℂ) x := by
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := (hasDerivAt_id x).ofReal_comp
      simpa using h1.const_mul (((-(Real.pi * (y + u)) : ℝ)) : ℂ)
    have h2 := (Complex.hasDerivAt_exp ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ))).scomp x hmul
    simpa [Function.comp_def, smul_eq_mul] using h2
  have hmain : HasDerivAt (fun x : ℝ => spikeKf C s y j x u)
      (C * ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹ * (((-(Real.pi * (y + u)) : ℝ)) : ℂ) ^ j *
        ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) *
          Complex.exp ((((-(Real.pi * (y + u)) : ℝ)) : ℂ) * (x : ℂ)))) x := by
    have hh := hbase.const_mul (C * ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹ *
      (((-(Real.pi * (y + u)) : ℝ)) : ℂ) ^ j)
    simpa [spikeKf, mul_assoc] using hh
  refine hmain.congr_deriv ?_
  simp only [spikeKf]
  ring

lemma jointContinuous_spikeKf (C : ℂ) (s y : ℝ) (hs : s ≠ 0) (j : ℕ) :
    Continuous (Function.uncurry (spikeKf C s y j)) := by
  have hbase : Continuous (fun p : ℝ × ℝ => ((s : ℂ) + (p.2 : ℂ) * Complex.I)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun p h => by
      have h1 := congrArg Complex.re h
      simp at h1
      exact hs h1)
  have hc : Continuous (fun p : ℝ × ℝ => (((-(Real.pi * (y + p.2)) : ℝ)) : ℂ) ^ j) := by fun_prop
  have hexp : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((((-(Real.pi * (y + p.2)) : ℝ)) : ℂ) * (p.1 : ℂ))) := by fun_prop
  exact ((continuous_const.mul hbase).mul hc).mul hexp

theorem laplace_pole_iteratedDeriv (C : ℂ) (s y ρ : ℝ) (hρ : 0 < ρ) (hs : s ≠ 0) (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun x : ℝ => ∫ u in (-ρ)..ρ,
        C * ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹ * Complex.exp (-(Real.pi * x * (y + u)))) x
      = ∫ u in (-ρ)..ρ, C * ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹ *
          ((-(Real.pi * (y + u)) : ℝ) : ℂ) ^ m * Complex.exp (-(Real.pi * x * (y + u))) := by
  have hρle : -ρ ≤ ρ := by linarith
  have hmain : ∀ m : ℕ, iteratedDeriv m (fun x : ℝ => ∫ u in (-ρ)..ρ, spikeKf C s y 0 x u)
      = fun x : ℝ => ∫ u in (-ρ)..ρ, spikeKf C s y m x u := by
    intro m
    induction m with
    | zero => rw [iteratedDeriv_zero]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x₀
      obtain ⟨B, hB⟩ := (isCompact_closedBall x₀ 1).prod isCompact_Icc |>.exists_bound_of_continuousOn
        ((jointContinuous_spikeKf C s y hs (j+1)).continuousOn.mono (Set.subset_univ _))
      have hbound : ∀ u : ℝ, u ∈ Set.uIoc (-ρ) ρ → ∀ x : ℝ, x ∈ Metric.ball x₀ 1 →
          ‖spikeKf C s y (j+1) x u‖ ≤ B := by
        intro u hu x hx
        rw [Set.uIoc_of_le hρle] at hu
        exact hB (x, u) ⟨Metric.ball_subset_closedBall hx, ⟨le_of_lt hu.1, hu.2⟩⟩
      have hdiff : ∀ u : ℝ, u ∈ Set.uIoc (-ρ) ρ → ∀ x : ℝ, x ∈ Metric.ball x₀ 1 →
          HasDerivAt (fun x : ℝ => spikeKf C s y j x u) (spikeKf C s y (j+1) x u) x :=
        fun u _ x _ => hasDerivAt_spikeKf C s y hs j x u
      have hstep := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun x u => spikeKf C s y j x u) (F' := fun x u => spikeKf C s y (j+1) x u)
        (x₀ := x₀) (s := Metric.ball x₀ 1) (bound := fun _ => B) (μ := volume)
        (Metric.ball_mem_nhds x₀ one_pos)
        (Filter.Eventually.of_forall (fun x => (continuous_spikeKf C s y hs j x).aestronglyMeasurable))
        ((continuous_spikeKf C s y hs j x₀).intervalIntegrable (-ρ) ρ)
        ((continuous_spikeKf C s y hs (j+1) x₀).aestronglyMeasurable)
        (Filter.Eventually.of_forall hbound)
        (intervalIntegrable_const (c := B))
        (Filter.Eventually.of_forall hdiff)
      have hder : deriv (fun x : ℝ => ∫ u in (-ρ)..ρ, spikeKf C s y j x u) x₀
          = ∫ u in (-ρ)..ρ, spikeKf C s y (j+1) x₀ u := hstep.2.deriv
      rw [hder]
  have hlhs : (fun x : ℝ => ∫ u in (-ρ)..ρ,
        C * ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹ * Complex.exp (-(Real.pi * x * (y + u))))
      = (fun x : ℝ => ∫ u in (-ρ)..ρ, spikeKf C s y 0 x u) := by
    funext x
    apply intervalIntegral.integral_congr
    intro u _
    simp only [spikeKf, pow_zero, mul_one]
    rw [← karg y x u]
  rw [hlhs, congrFun (hmain m) x]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [spikeKf]
  rw [karg y x u]



private lemma lowRho_pos : 0 < lowRho := by norm_num [lowRho]

/-- Rewrite `PhiSpike` as an interval integral in the `u = t - Im τ` variable. -/
private lemma PhiSpike_rewrite (τ : ℍ) (x : ℝ) :
    PhiSpike τ x = ((tsign τ : ℂ) / (2 * Real.pi)) *
      ∫ u in (-lowRho)..lowRho,
        ((((tsign τ - τ.re : ℝ)) : ℂ) + (u : ℂ) * Complex.I)⁻¹ *
          Complex.exp (-(Real.pi * x * (τ.im + u))) := by
  have hτcoe : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (τ : ℂ)]
    simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  unfold PhiSpike lowWin
  rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := τ.im - lowRho) (b := τ.im + lowRho))]
  rw [← intervalIntegral.integral_of_le (by linarith [lowRho_pos] : τ.im - lowRho ≤ τ.im + lowRho)]
  rw [show τ.im - lowRho = τ.im + (-lowRho) by ring]
  rw [← intervalIntegral.integral_comp_add_left
        (fun t => tpole τ t * Complex.exp (-(Real.pi * x * t))) τ.im]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  have hd : ((τ.im + u : ℝ) : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))
      = ((((tsign τ - τ.re : ℝ)) : ℂ) + (u : ℂ) * Complex.I) := by
    rw [hτcoe]; push_cast; ring
  simp only [tpole]
  rw [hd, div_eq_mul_inv]
  have harg : (-((Real.pi : ℂ) * (x : ℂ) * ↑(τ.im + u)))
      = -((Real.pi : ℂ) * (u : ℂ) * (x : ℂ)) - (Real.pi : ℂ) * (x : ℂ) * (τ.im : ℂ) := by
    push_cast; ring
  rw [harg]
  ring

private lemma one_add_mul_exp_neg_le (a : ℝ) (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) * Real.exp (-(a * t)) ≤ B := by
  refine ⟨1 + 1 / (a * Real.exp 1), by positivity, fun t ht => ?_⟩
  have h1 : a * t * Real.exp (-(a * t)) ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one (a * t)
  have h2 : a * Real.exp (-(a * t)) ≤ a := by
    have h3 : Real.exp (-(a * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [ha, ht]
    nlinarith [ha.le, h3]
  have hkey : (1 + t) * Real.exp (-(a * t))
      = (1 / a) * (a * Real.exp (-(a * t)) + a * t * Real.exp (-(a * t))) := by
    field_simp
  have hEq : (1 / a) * (a + Real.exp (-1)) = 1 + 1 / (a * Real.exp 1) := by
    rw [show Real.exp (-1) = (Real.exp 1)⁻¹ from Real.exp_neg 1]
    field_simp
  calc (1 + t) * Real.exp (-(a * t))
      = (1 / a) * (a * Real.exp (-(a * t)) + a * t * Real.exp (-(a * t))) := hkey
    _ ≤ (1 / a) * (a + Real.exp (-1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 1 + 1 / (a * Real.exp 1) := hEq

private lemma exists_exp_poly_bound (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x →
      (1 + Real.pi * x) * Real.exp (-(c * x)) ≤ K * (1 + x) ^ (-(N : ℝ)) := by
  set a : ℝ := c / ((N : ℝ) + 1) with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  obtain ⟨B, hB0, hB⟩ := one_add_mul_exp_neg_le a ha
  refine ⟨Real.pi * B ^ (N + 1), by positivity, fun x hx => ?_⟩
  have hxpos : 0 < 1 + x := by linarith
  have h1 : 1 + Real.pi * x ≤ Real.pi * (1 + x) := by nlinarith [Real.pi_gt_three]
  have h2 : (1 + x) ^ (N + 1) * Real.exp (-(c * x)) ≤ B ^ (N + 1) := by
    have hbase : (1 + x) * Real.exp (-(a * x)) ≤ B := hB x hx
    have hpow : ((1 + x) * Real.exp (-(a * x))) ^ (N + 1) ≤ B ^ (N + 1) :=
      pow_le_pow_left₀ (by positivity) hbase (N + 1)
    have heq : ((1 + x) * Real.exp (-(a * x))) ^ (N + 1)
        = (1 + x) ^ (N + 1) * Real.exp (-(c * x)) := by
      rw [mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      rw [ha_def]
      field_simp
      push_cast
      ring
    rwa [heq] at hpow
  have key : (1 + Real.pi * x) * Real.exp (-(c * x)) * (1 + x) ^ N ≤ Real.pi * B ^ (N + 1) := by
    have step1 : (1 + Real.pi * x) * Real.exp (-(c * x)) * (1 + x) ^ N
        ≤ Real.pi * ((1 + x) ^ (N + 1) * Real.exp (-(c * x))) := by
      have hEx : 0 ≤ Real.exp (-(c * x)) := Real.exp_nonneg _
      calc (1 + Real.pi * x) * Real.exp (-(c * x)) * (1 + x) ^ N
          ≤ (Real.pi * (1 + x)) * Real.exp (-(c * x)) * (1 + x) ^ N := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right h1 hEx
        _ = Real.pi * ((1 + x) ^ (N + 1) * Real.exp (-(c * x))) := by rw [pow_succ]; ring
    calc (1 + Real.pi * x) * Real.exp (-(c * x)) * (1 + x) ^ N
        ≤ Real.pi * ((1 + x) ^ (N + 1) * Real.exp (-(c * x))) := step1
      _ ≤ Real.pi * B ^ (N + 1) := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have hdiv : Real.pi * B ^ (N + 1) * ((1 + x) ^ N)⁻¹ = Real.pi * B ^ (N + 1) / (1 + x) ^ N := by
    rw [div_eq_mul_inv]
  rw [Real.rpow_neg hxpos.le, Real.rpow_natCast, hdiv,
    le_div_iff₀ (by positivity : (0:ℝ) < (1 + x) ^ N)]
  exact key



/-- Shifting the simple pole `(s + iu)⁻¹` to the model form `(u + iε)⁻¹` with `ε = -s`. -/
private lemma spike_inv_shift (s u : ℝ) :
    ((s : ℂ) + (u : ℂ) * Complex.I)⁻¹
      = -Complex.I * (((u : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹) := by
  have h2 : ((s : ℂ) + (u : ℂ) * Complex.I)
      = Complex.I * ((u : ℂ) + ((-s : ℝ) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_neg, mul_add]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h2, mul_inv_rev, Complex.inv_I]
  ring

/-- `(↑(-(π(y+u))))^m = (↑((-π)^m)) · (↑y + ↑u)^m`. -/
private lemma spike_pow_shift (y u : ℝ) (m : ℕ) :
    ((((-(Real.pi * (y + u)) : ℝ)) : ℂ)) ^ m
      = ((((-Real.pi) ^ m : ℝ)) : ℂ) * ((y : ℂ) + (u : ℂ)) ^ m := by
  rw [show (((-(Real.pi * (y + u)) : ℝ)) : ℂ)
        = (((-Real.pi : ℝ) : ℂ)) * ((y : ℂ) + (u : ℂ)) by push_cast; ring]
  rw [mul_pow, ← Complex.ofReal_pow]

/-- Casting the Laplace weight: `e^{-πx(y+u)} = exp(-↑(πx) · (↑y + ↑u))`. -/
private lemma spike_exp_shift (x y u : ℝ) :
    Complex.exp (-(Real.pi * x * (y + u)))
      = Complex.exp (-(((Real.pi * x : ℝ)) : ℂ) * ((y : ℂ) + (u : ℂ))) := by
  congr 1
  push_cast
  ring

theorem lowBad_PhiSpike_deriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (m N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => Work.Asymptotics.HalfFunnel.PhiSpike τ x) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)) := by
  obtain ⟨Cm, hCm0, hCmb⟩ := spike_model_integral_decay m (ρ := lowRho) (Y := 2)
    lowRho_pos (by norm_num [lowRho])
  obtain ⟨Kp, hKp0, hKpb⟩ := exists_exp_poly_bound (3 * Real.pi / 8) (by positivity) N
  refine ⟨Real.pi ^ m / (2 * Real.pi) * Cm * Kp, by positivity, ?_⟩
  intro τ hτ x hx
  have hDD : τ ∈ Work.Asymptotics.DomainD := hτ.1
  have him1 : (1:ℝ)/2 ≤ τ.im := hτ.2.1
  have him2 : τ.im ≤ 2 := hτ.2.2.1
  have hre := hτ.2.2.2
  have hre1 : -1 < τ.re := hDD.1
  have hre2 : τ.re < 1 := hDD.2.1
  set s : ℝ := tsign τ - τ.re with hs_def
  have htsign_abs : |tsign τ| = 1 := by unfold tsign; split_ifs <;> norm_num
  have hs_abs : |s| ≤ 1/4 := by
    rcases hre with h | h
    · have ht : tsign τ = 1 := by unfold tsign; rw [if_pos (by linarith)]
      rw [hs_def, ht, abs_le]; constructor <;> linarith
    · have ht : tsign τ = -1 := by unfold tsign; rw [if_neg (by linarith)]
      rw [hs_def, ht, abs_le]; constructor <;> linarith
  have hs_ne : s ≠ 0 := by
    rcases hre with h | h
    · have ht : tsign τ = 1 := by unfold tsign; rw [if_pos (by linarith)]
      rw [hs_def, ht]; linarith
    · have ht : tsign τ = -1 := by unfold tsign; rw [if_neg (by linarith)]
      rw [hs_def, ht]; linarith
  have hlowRho : lowRho = 1/8 := by norm_num [lowRho]
  have hy1 : lowRho < τ.im := by linarith [hlowRho, him1]
  have hy3 : (3:ℝ)/8 ≤ τ.im - lowRho := by linarith [hlowRho, him1]
  have hfund : (fun x : ℝ => PhiSpike τ x)
      = (fun x : ℝ => ∫ u in (-lowRho)..lowRho,
          ((tsign τ : ℂ) / (2 * Real.pi)) * (((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) *
            Complex.exp (-(Real.pi * x * (τ.im + u)))) := by
    funext y
    rw [PhiSpike_rewrite τ y]
    have hs_coe : (((tsign τ - τ.re : ℝ)) : ℂ) = (s : ℂ) := by rw [hs_def]
    rw [hs_coe, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [hfund,
    laplace_pole_iteratedDeriv ((tsign τ : ℂ) / (2 * Real.pi)) s τ.im lowRho lowRho_pos hs_ne m x]
  have hpt : ∀ u : ℝ, ((tsign τ : ℂ) / (2 * Real.pi)) * (((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) *
        ((((-(Real.pi * (τ.im + u)) : ℝ)) : ℂ)) ^ m * Complex.exp (-(Real.pi * x * (τ.im + u)))
      = (((tsign τ : ℂ) / (2 * Real.pi)) * (-Complex.I) * ((((-Real.pi) ^ m : ℝ)) : ℂ)) *
        (Complex.exp (-(((Real.pi * x : ℝ)) : ℂ) * ((τ.im : ℂ) + (u : ℂ))) *
          (((u : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹) * ((τ.im : ℂ) + (u : ℂ)) ^ m) := by
    intro u
    rw [spike_inv_shift s u, spike_pow_shift τ.im u m, spike_exp_shift x τ.im u]
    ring
  have hcongr : (∫ u in (-lowRho)..lowRho, ((tsign τ : ℂ) / (2 * Real.pi)) *
        (((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) * ((((-(Real.pi * (τ.im + u)) : ℝ)) : ℂ)) ^ m *
        Complex.exp (-(Real.pi * x * (τ.im + u))))
      = (((tsign τ : ℂ) / (2 * Real.pi)) * (-Complex.I) * ((((-Real.pi) ^ m : ℝ)) : ℂ)) *
        ∫ u in (-lowRho)..lowRho,
          (Complex.exp (-(((Real.pi * x : ℝ)) : ℂ) * ((τ.im : ℂ) + (u : ℂ))) *
            (((u : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹) * ((τ.im : ℂ) + (u : ℂ)) ^ m) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    exact hpt u
  rw [hcongr, norm_mul]
  have hConstnorm : ‖((tsign τ : ℂ) / (2 * Real.pi)) * (-Complex.I) *
      ((((-Real.pi) ^ m : ℝ)) : ℂ)‖ = Real.pi ^ m / (2 * Real.pi) := by
    have hC' : ‖((tsign τ : ℂ) / (2 * Real.pi))‖ = 1 / (2 * Real.pi) := by
      have h1 : ‖(tsign τ : ℂ)‖ = 1 := by rw [Complex.norm_real, Real.norm_eq_abs, htsign_abs]
      have h2a : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h2b : ‖(Real.pi : ℂ)‖ = Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have h2 : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul, h2a, h2b]
      rw [norm_div, h1, h2]
    rw [norm_mul, norm_mul, hC', norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_pow, abs_neg, abs_of_pos Real.pi_pos]
    ring
  rw [hConstnorm]
  have hmodel := hCmb τ.im (Real.pi * x) (-s) hy1 him2 (by positivity)
    (by simpa using hs_ne) (by simpa using hs_abs)
  calc Real.pi ^ m / (2 * Real.pi) *
        ‖∫ u in (-lowRho)..lowRho, Complex.exp (-(((Real.pi * x : ℝ)) : ℂ) * ((τ.im : ℂ) + (u : ℂ))) *
            (((u : ℂ) + ((-s : ℝ) : ℂ) * Complex.I)⁻¹) * ((τ.im : ℂ) + (u : ℂ)) ^ m‖
      ≤ Real.pi ^ m / (2 * Real.pi) *
          (Cm * (1 + Real.pi * x) * Real.exp (-(Real.pi * x * (τ.im - lowRho)))) :=
        mul_le_mul_of_nonneg_left hmodel (by positivity)
    _ ≤ Real.pi ^ m / (2 * Real.pi) *
          (Cm * (1 + Real.pi * x) * Real.exp (-(3 * Real.pi / 8 * x))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]
        have hprod : (0:ℝ) ≤ (Real.pi * x) * ((τ.im - lowRho) - 3/8) :=
          mul_nonneg (mul_nonneg Real.pi_pos.le hx) (by linarith)
        nlinarith [hprod]
    _ = Real.pi ^ m / (2 * Real.pi) * Cm * ((1 + Real.pi * x) * Real.exp (-(3 * Real.pi / 8 * x))) := by
        ring
    _ ≤ Real.pi ^ m / (2 * Real.pi) * Cm * (Kp * (1 + x) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left (hKpb x hx) (by positivity)
    _ = (Real.pi ^ m / (2 * Real.pi) * Cm * Kp) * (1 + x) ^ (-(N : ℝ)) := by ring


end Work.Asymptotics.HalfFunnel
