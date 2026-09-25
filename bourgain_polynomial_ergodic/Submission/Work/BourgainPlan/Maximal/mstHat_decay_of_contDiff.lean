import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Commons.Analysis.Fourier.fourier_transform_min_decay

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- The `C²` version of the bump-transform decay.  Needs
`Submission.Commons.Analysis.Fourier.fourier_transform_min_decay` (second differences),
`Submission.Commons.Analysis.Calculus.integral_second_difference_le_sq`, and
`Work.BourgainPlan.Maximal.mstHat` from `mst_err1_bump_defs`.  Route: `mstHat Ξ t = 𝓕 Ξ t`
(the integral over `(-1/2,1/2)` is the integral over `ℝ` since `Ξ` vanishes off `(-1/2,1/2)`),
then two-fold integration by parts for an `L¹` bound on `Ξ''`. -/
theorem mstHat_decay_of_contDiff (Ξ : ℝ → ℂ) (hcd : ContDiff ℝ 2 Ξ)
    (hsupp : ∀ x : ℝ, 1 / 2 < |x| → Ξ x = 0) :
    ∀ t : ℝ, t ≠ 0 →
      ‖Work.BourgainPlan.Maximal.mstHat Ξ t‖
        ≤ (∫ x, ‖deriv (deriv Ξ) x‖) / (2 * Real.pi) ^ 2 / t ^ 2 := by
  -- `Ξ` vanishes off the closed fundamental interval
  have hzero : ∀ x : ℝ, x ∉ Set.Icc (-(1/2) : ℝ) (1/2) → Ξ x = 0 := by
    intro x hx
    apply hsupp
    by_contra h
    have hle : |x| ≤ 1 / 2 := not_lt.mp h
    exact hx (by rw [Set.mem_Icc]; exact abs_le.mp hle)
  have hcs : HasCompactSupport Ξ := HasCompactSupport.intro isCompact_Icc hzero
  -- integrability of `Ξ` and of its second derivative
  have hint0 : Integrable Ξ := hcd.continuous.integrable_of_hasCompactSupport hcs
  have hcont2 : Continuous (deriv (deriv Ξ)) := by
    have h := hcd.continuous_iteratedDeriv 2 le_rfl
    have hid : iteratedDeriv 2 Ξ = deriv (deriv Ξ) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rwa [hid] at h
  have hint2 : Integrable (deriv (deriv Ξ)) :=
    hcont2.integrable_of_hasCompactSupport hcs.deriv.deriv
  have hdiff1 : Differentiable ℝ Ξ := hcd.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (deriv Ξ) := by
    have h := hcd.differentiable_iteratedDeriv' 1
    rwa [iteratedDeriv_one] at h
  -- The Fourier transform of `Ξ`, read off the fundamental interval
  have hFourier_eq : ∀ t : ℝ, FourierTransform.fourier Ξ t =
      ∫ x in Set.Ioo (-(1/2) : ℝ) (1/2),
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • Ξ x := by
    intro t
    rw [Real.fourier_eq' Ξ t]
    have h1 : ∀ x ∉ Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • Ξ x = 0 :=
      fun x hx => by rw [hzero x hx, smul_zero]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hmstHat_eq : ∀ t : ℝ, mstHat Ξ t =
      ∫ x in Set.Ioo (-(1/2) : ℝ) (1/2),
        Ξ x * Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [mstHat_apply, intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hpt : ∀ t : ℝ, Set.EqOn
      (fun x : ℝ => Ξ x * Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I))
      (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) • Ξ x)
      (Set.Ioo (-(1/2) : ℝ) (1/2)) := by
    intro t x _
    dsimp only
    have hexp : Complex.exp ((((-(2 * Real.pi * t * x)) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) * Complex.I)) := by
      congr 1
      simp only [Real.inner_apply]
      push_cast
      ring
    rw [hexp, smul_eq_mul]
    ring
  have hmstHat : ∀ t : ℝ, mstHat Ξ t = FourierTransform.fourier Ξ t := by
    intro t
    rw [hmstHat_eq t, hFourier_eq t,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (hpt t)]
  -- two-fold integration by parts via `fourier_transform_min_decay`
  set B : ℝ := ∫ x, ‖deriv (deriv Ξ) x‖ with hB
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun x => norm_nonneg _)
  have hA0 : 0 ≤ ∫ x, ‖Ξ x‖ := integral_nonneg (fun x => norm_nonneg _)
  intro t ht
  rw [hmstHat t]
  have hdec := Commons.Analysis.Fourier.fourier_transform_min_decay Ξ (∫ x, ‖Ξ x‖) B hA0 hB0
    hint0 hint2 hdiff1 hdiff2 le_rfl le_rfl t ht
  have h1 : ‖FourierTransform.fourier Ξ t‖ ≤ B / (2 * Real.pi * |t|) ^ 2 :=
    hdec.trans (min_le_right _ _)
  have h2 : B / (2 * Real.pi * |t|) ^ 2 = B / (2 * Real.pi) ^ 2 / t ^ 2 := by
    rw [mul_pow, sq_abs, ← div_div]
  rwa [h2] at h1

end

end Work.BourgainPlan.Maximal
