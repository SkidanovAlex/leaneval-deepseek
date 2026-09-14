import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Integral.integral_inv_affine_cos_pi_mul

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral
open scoped Real

/-- For `s ≥ √2` the two entries of the `max` coincide with `s - cos θ`. -/
private lemma sup_circle_integrand_eq {s : ℝ} (hs : Real.sqrt 2 ≤ s) (θ : ℝ) :
    (max |s - Real.cos θ| |Real.sin θ|)⁻¹ = (s - Real.cos θ)⁻¹ := by
  have hs1 : 1 < s := lt_of_lt_of_le Real.one_lt_sqrt_two hs
  have hpos : 0 < s - Real.cos θ := by
    have := Real.cos_le_one θ
    linarith
  have hs2 : (2 : ℝ) ≤ s ^ 2 := by
    have h2 : Real.sqrt 2 ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg 2) hs 2
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h2
  have hsq : Real.sin θ ^ 2 ≤ (s - Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ - s / 2)]
  have hle : |Real.sin θ| ≤ s - Real.cos θ := by
    have h : Real.sqrt (Real.sin θ ^ 2) ≤ Real.sqrt ((s - Real.cos θ) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hpos] at h
  have ha : |Real.sin θ| ≤ |s - Real.cos θ| := by rwa [abs_of_pos hpos]
  rw [max_eq_left ha, abs_of_pos hpos]

/-- Reduction of the circle mean of `(s - cos θ)⁻¹` to the basic affine-cosine integral. -/
private lemma inv_sub_cos_circle_mean {s : ℝ} (hs : 1 < s) :
    (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (s - Real.cos θ)⁻¹
      = (Real.sqrt (s ^ 2 - 1))⁻¹ := by
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hsne : ∀ θ : ℝ, s - Real.cos θ ≠ 0 := by
    intro θ
    have := Real.cos_le_one θ
    exact ne_of_gt (by linarith : 0 < s - Real.cos θ)
  have hcontA : Continuous (fun x : ℝ => (s - Real.cos (2 * Real.pi * x))⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun x => hsne (2 * Real.pi * x))
  have hcontB : Continuous (fun x : ℝ => (s - Real.cos (Real.pi * x))⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun x => hsne (Real.pi * x))
  -- Step 1: rescale (0, 2π) to (0, 1)
  have step1 : (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (s - Real.cos θ)⁻¹
      = ∫ x in (0 : ℝ)..1, (s - Real.cos (2 * Real.pi * x))⁻¹ := by
    have hcomp : (∫ x in (0 : ℝ)..1, (s - Real.cos (2 * Real.pi * x))⁻¹)
        = (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi), (s - Real.cos θ)⁻¹ := by
      have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
        (fun θ : ℝ => (s - Real.cos θ)⁻¹) h2pi
      simpa only [mul_zero, mul_one, smul_eq_mul] using h
    rw [hcomp, one_div]
  -- Step 2: fold (0,1) with cos (2π x) to (0,1) with cos (π x)
  have step2 : (∫ x in (0 : ℝ)..1, (s - Real.cos (2 * Real.pi * x))⁻¹)
      = ∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * x))⁻¹ := by
    have hsum : (∫ x in (0 : ℝ)..(1 / 2), (s - Real.cos (2 * Real.pi * x))⁻¹)
          + (∫ x in (1 / 2 : ℝ)..1, (s - Real.cos (2 * Real.pi * x))⁻¹)
        = ∫ x in (0 : ℝ)..1, (s - Real.cos (2 * Real.pi * x))⁻¹ :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcontA.intervalIntegrable (0 : ℝ) (1 / 2))
        (hcontA.intervalIntegrable (1 / 2) 1)
    have hreflect : (∫ x in (1 / 2 : ℝ)..1, (s - Real.cos (2 * Real.pi * x))⁻¹)
        = ∫ x in (0 : ℝ)..(1 / 2), (s - Real.cos (2 * Real.pi * x))⁻¹ := by
      have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 / 2))
        (fun x : ℝ => (s - Real.cos (2 * Real.pi * x))⁻¹) 1
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
          show (1 : ℝ) - 0 = 1 by norm_num] at h
      have hcongr : (∫ x in (0 : ℝ)..(1 / 2), (s - Real.cos (2 * Real.pi * (1 - x)))⁻¹)
          = ∫ x in (0 : ℝ)..(1 / 2), (s - Real.cos (2 * Real.pi * x))⁻¹ := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        show (s - Real.cos (2 * Real.pi * (1 - x)))⁻¹ = (s - Real.cos (2 * Real.pi * x))⁻¹
        rw [show 2 * Real.pi * (1 - x) = 2 * Real.pi - 2 * Real.pi * x by ring,
            Real.cos_two_pi_sub]
      exact h.symm.trans hcongr
    have hhalf : (∫ x in (0 : ℝ)..(1 / 2), (s - Real.cos (2 * Real.pi * x))⁻¹)
        = (1 / 2) * ∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * x))⁻¹ := by
      have h := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := 1)
        (fun x : ℝ => (s - Real.cos (2 * Real.pi * x))⁻¹) (show (2 : ℝ) ≠ 0 by norm_num)
      rw [show (0 : ℝ) / 2 = 0 by norm_num,
          show (1 : ℝ) / 2 = 1 / 2 by norm_num, smul_eq_mul] at h
      have hcongr : (∫ x in (0 : ℝ)..1, (s - Real.cos (2 * Real.pi * (x / 2)))⁻¹)
          = ∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * x))⁻¹ := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        show (s - Real.cos (2 * Real.pi * (x / 2)))⁻¹ = (s - Real.cos (Real.pi * x))⁻¹
        rw [show 2 * Real.pi * (x / 2) = Real.pi * x by ring]
      rw [hcongr] at h
      linarith
    rw [hreflect, hhalf] at hsum
    rw [← hsum]
    ring
  -- Step 3: reflection v ↦ 1 - v on cos (π x)
  have step3 : (∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * x))⁻¹)
      = ∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * (1 - x)))⁻¹ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => (s - Real.cos (Real.pi * x))⁻¹) 1
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 0 = 1 by norm_num] at h
    exact h.symm
  -- Step 4: the classical integral
  have step4 : (∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * (1 - x)))⁻¹)
      = (Real.sqrt (s ^ 2 - 1))⁻¹ := by
    have h := integral_inv_affine_cos_pi_mul (A := s) (B := 1) (by norm_num) hs
    have hcongr : (∫ x in (0 : ℝ)..1, (s - Real.cos (Real.pi * (1 - x)))⁻¹)
        = ∫ x in (0 : ℝ)..1, (s + 1 * Real.cos (Real.pi * x))⁻¹ := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show (s - Real.cos (Real.pi * (1 - x)))⁻¹ = (s + 1 * Real.cos (Real.pi * x))⁻¹
      rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring, Real.cos_pi_sub]
      ring
    rw [hcongr]
    simpa using h
  rw [step1, step2, step3, step4]

theorem sup_circle_mean_eq_large_s {s : ℝ} (hs : Real.sqrt 2 ≤ s) :
    (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
        (max |s - Real.cos θ| |Real.sin θ|)⁻¹
      = (Real.sqrt (s ^ 2 - 1))⁻¹ := by
  have hs1 : 1 < s := lt_of_lt_of_le Real.one_lt_sqrt_two hs
  rw [intervalIntegral.integral_congr
        (fun θ _ => sup_circle_integrand_eq hs θ)]
  exact inv_sub_cos_circle_mean hs1

end Commons.Analysis.Integral