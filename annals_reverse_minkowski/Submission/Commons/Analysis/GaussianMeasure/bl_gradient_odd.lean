import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated
import Submission.Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory

set_option maxHeartbeats 4000000

theorem bl_gradient_odd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (f h : E → ℝ) (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x) (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hh : ContDiff ℝ 1 h) (hodd : ∀ x : E, h (-x) = -h x) (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |h x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) : 2 * Real.pi * (∫ x, h x ^ 2 * Real.exp (-(f x))) ≤ ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := by
  classical
  obtain ⟨Ch, hCh0, Nh, hghb⟩ := hgh
  -- Operator-norm growth bound for the derivative of `h`
  have hfderiv_bound : ∀ x : E, ‖fderiv ℝ h x‖ ≤ Ch * (1 + ‖x‖) ^ Nh := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hCh0 (pow_nonneg (by positivity) _)) ?_
    intro v
    rw [Real.norm_eq_abs]
    exact (hghb x v).2
  -- Continuity of `x ↦ grad h x`
  have hgrad_cont : Continuous (fun x : E => grad h x) := by
    have h1 : Continuous (fun x : E => fderiv ℝ h x) := hh.continuous_fderiv one_ne_zero
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp h1
  -- Integrability of the RHS integrand `‖fderiv h‖ ^ 2 * exp (-f)`
  have hRint : Integrable (fun x : E => ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) := by
    refine integrable_mul_exp_neg_stronglyConvex f (fun x : E => ‖fderiv ℝ h x‖ ^ 2) hf hconv
      ((hh.continuous_fderiv one_ne_zero).norm.pow 2) (Ch ^ 2) (sq_nonneg Ch) (2 * Nh) ?_
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    calc ‖fderiv ℝ h x‖ ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hfderiv_bound x) 2
      _ = Ch ^ 2 * (1 + ‖x‖) ^ (2 * Nh) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm]
  -- Integrability of the Brascamp–Lieb energy integrand
  have hDcont : Continuous
      (fun x : E => inner ℝ (hessInv f x (grad h x)) (grad h x)) :=
    Continuous.inner
      ((continuous_hessInv_pair f hf hH).comp (continuous_id.prodMk hgrad_cont)) hgrad_cont
  have hDint : Integrable
      (fun x : E => inner ℝ (hessInv f x (grad h x)) (grad h x) * Real.exp (-(f x))) := by
    refine integrable_mul_exp_neg_stronglyConvex f
      (fun x : E => inner ℝ (hessInv f x (grad h x)) (grad h x)) hf hconv hDcont
      (Ch ^ 2 / (2 * Real.pi)) (by positivity) (2 * Nh) ?_
    intro x
    have hinj : Function.Injective (hessOp f x) := hessOp_injective f x (hH x)
    have h1 : ‖hessInv f x (grad h x)‖ ≤ ‖grad h x‖ / (2 * Real.pi) :=
      hessInv_norm_le f x hinj (hH x) (grad h x)
    have h2 : |inner ℝ (hessInv f x (grad h x)) (grad h x)|
        ≤ ‖hessInv f x (grad h x)‖ * ‖grad h x‖ := by
      rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
    have h3 : ‖grad h x‖ ≤ Ch * (1 + ‖x‖) ^ Nh := by
      rw [grad_norm_eq]; exact hfderiv_bound x
    have hπ : (0:ℝ) < 2 * Real.pi := by positivity
    have h4 : ‖hessInv f x (grad h x)‖ * ‖grad h x‖ ≤ ‖grad h x‖ ^ 2 / (2 * Real.pi) := by
      calc ‖hessInv f x (grad h x)‖ * ‖grad h x‖
          ≤ (‖grad h x‖ / (2 * Real.pi)) * ‖grad h x‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖grad h x‖ ^ 2 / (2 * Real.pi) := by ring
    have h5 : ‖grad h x‖ ^ 2 / (2 * Real.pi) ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h3 2) hπ.le
    calc |inner ℝ (hessInv f x (grad h x)) (grad h x)|
        ≤ ‖hessInv f x (grad h x)‖ * ‖grad h x‖ := h2
      _ ≤ ‖grad h x‖ ^ 2 / (2 * Real.pi) := h4
      _ ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 / (2 * Real.pi) := h5
      _ = Ch ^ 2 / (2 * Real.pi) * (1 + ‖x‖) ^ (2 * Nh) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm]; ring
  -- Oddness: `∫ h · exp (-f) = 0`
  have hB0 : (∫ x : E, h x * Real.exp (-(f x))) = 0 := by
    set G : E → ℝ := fun y => h y * Real.exp (-(f y)) with hG
    have hcomp := integral_comp_isometry (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) G
    have hneg : ∀ x : E, G ((LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) x) = -G x := by
      intro x
      show G (-x) = -G x
      simp only [hG]
      rw [hodd x, hfe x]
      ring
    have h1 : (∫ y : E, G y) = ∫ x : E, -G x := by
      rw [← hcomp]
      exact integral_congr_ae (Filter.Eventually.of_forall hneg)
    rw [integral_neg] at h1
    have hGint : (∫ y : E, G y) = ∫ x : E, h x * Real.exp (-(f x)) := by simp only [hG]
    rw [hGint] at h1
    linarith
  -- Pointwise bound on the Brascamp–Lieb energy integrand
  have hpoint : ∀ x : E,
      inner ℝ (hessInv f x (grad h x)) (grad h x) * Real.exp (-(f x))
        ≤ (1 / (2 * Real.pi)) * (‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) := by
    intro x
    have hinj : Function.Injective (hessOp f x) := hessOp_injective f x (hH x)
    have h1 : inner ℝ (hessInv f x (grad h x)) (grad h x) ≤ ‖grad h x‖ ^ 2 / (2 * Real.pi) :=
      hessInv_energy f x hinj (hH x) (grad h x)
    have h2 : ‖grad h x‖ ^ 2 = ‖fderiv ℝ h x‖ ^ 2 := by rw [grad_norm_eq]
    have h3 : inner ℝ (hessInv f x (grad h x)) (grad h x) * Real.exp (-(f x))
        ≤ (‖fderiv ℝ h x‖ ^ 2 / (2 * Real.pi)) * Real.exp (-(f x)) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    refine h3.trans (le_of_eq ?_)
    ring
  -- Energy bound: `∫ ⟪hessInv ∇h, ∇h⟫ exp (-f) ≤ (1/2π) ∫ ‖fderiv h‖ ^ 2 exp (-f)`
  have hDle : (∫ x : E, inner ℝ (hessInv f x (grad h x)) (grad h x) * Real.exp (-(f x)))
      ≤ (1 / (2 * Real.pi)) * (∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) := by
    have hQint : Integrable
        (fun x : E => (1 / (2 * Real.pi)) * (‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)))) :=
      hRint.const_mul _
    have hmono := integral_mono hDint hQint hpoint
    rwa [integral_const_mul] at hmono
  -- Brascamp–Lieb plus oddness
  have hBL := brascamp_lieb_smooth f h hf hH hconv hgf hh ⟨Ch, hCh0, Nh, hghb⟩
  rw [hB0] at hBL
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at hBL
  have hAle : (∫ x : E, h x ^ 2 * Real.exp (-(f x)))
      ≤ (1 / (2 * Real.pi)) * (∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) :=
    le_trans hBL hDle
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hAle h2pi.le
  have hcancel : 2 * Real.pi * ((1 / (2 * Real.pi)) * (∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))))
      = ∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := by
    field_simp
  calc 2 * Real.pi * (∫ x, h x ^ 2 * Real.exp (-(f x)))
      ≤ 2 * Real.pi * ((1 / (2 * Real.pi)) * (∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)))) := hmul
    _ = ∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := hcancel

end Commons.Analysis.GaussianMeasure
