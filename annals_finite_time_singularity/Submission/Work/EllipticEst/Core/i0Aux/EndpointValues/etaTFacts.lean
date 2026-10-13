import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open MeasureTheory Set Filter

theorem etaTFacts {t : ℝ} (ht : 0 < t) :
    (∀ x : ℝ, HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT t)
      (Work.EllipticEst.Core.i0Aux.etaT' t x) x) ∧
    (∀ x : ℝ, HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT' t)
      (Work.EllipticEst.Core.i0Aux.etaT'' t x) x) ∧
    (Work.EllipticEst.Core.i0Aux.etaT t 0 = 0) ∧
    (Work.EllipticEst.Core.i0Aux.etaT' t 0 = 1) ∧
    (Work.EllipticEst.Core.i0Aux.etaT t t = 0) ∧
    (Work.EllipticEst.Core.i0Aux.etaT' t t = 0) ∧
    (∫ x in (0 : ℝ)..t, (Work.EllipticEst.Core.i0Aux.etaT t x) ^ 2 ≤ t ^ 3 / 3) ∧
    (∫ x in (0 : ℝ)..t, (Work.EllipticEst.Core.i0Aux.etaT'' t x) ^ 2 ≤ 36 / t) := by
  -- The first derivative: `η_t(x) = x (1 - x/t)^3`, product rule.
  have hder1 : ∀ x : ℝ, HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT t)
      (Work.EllipticEst.Core.i0Aux.etaT' t x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 - y / t) (-1 / t) x := by
      have h := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub ((hasDerivAt_id x).div_const t)
      convert h using 1
      · funext y; simp
      · ring
    have h2 : HasDerivAt (fun y : ℝ => (1 - y / t) ^ 3) (3 * (1 - x / t) ^ 2 * (-1 / t)) x :=
      h1.pow 3
    have h3 := (hasDerivAt_id x).mul h2
    convert h3 using 1
    · funext y; rfl
    · simp only [id_eq, Work.EllipticEst.Core.i0Aux.etaT']; ring
  -- The second derivative: `η_t'(x) = (1 - x/t)^2 (1 - 4x/t)`, product rule.
  have hder2 : ∀ x : ℝ, HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT' t)
      (Work.EllipticEst.Core.i0Aux.etaT'' t x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 - y / t) (-1 / t) x := by
      have h := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub ((hasDerivAt_id x).div_const t)
      convert h using 1
      · funext y; simp
      · ring
    have h4 : HasDerivAt (fun y : ℝ => 1 - 4 * y / t) (-4 / t) x := by
      have h := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        (((hasDerivAt_id x).const_mul (4 : ℝ)).div_const t)
      convert h using 1
      · funext y; simp [Pi.sub_apply]
      · ring
    have h5 := (h1.pow 2).mul h4
    convert h5 using 1
    · funext y; rfl
    · simp only [Pi.pow_apply, Work.EllipticEst.Core.i0Aux.etaT'']; ring
  refine ⟨hder1, hder2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Work.EllipticEst.Core.i0Aux.etaT]
  · simp [Work.EllipticEst.Core.i0Aux.etaT']
  · simp only [Work.EllipticEst.Core.i0Aux.etaT]
    field_simp
    ring
  · simp only [Work.EllipticEst.Core.i0Aux.etaT']
    field_simp
    ring
  · -- `∫_0^t η² ≤ t³/3`: pointwise `η(x)² ≤ x²`, then `∫_0^t x² = t³/3`.
    have hpt1 : ∀ x ∈ Set.Icc (0 : ℝ) t, (Work.EllipticEst.Core.i0Aux.etaT t x) ^ 2 ≤ x ^ 2 := by
      intro x hx
      obtain ⟨hx0, hxt⟩ := hx
      have hxt' : x / t ≤ 1 := (div_le_one ht).mpr hxt
      have hx0' : 0 ≤ x / t := div_nonneg hx0 (le_of_lt ht)
      have hu0 : 0 ≤ 1 - x / t := by linarith
      have hu1 : 1 - x / t ≤ 1 := by linarith
      have hu6 : (1 - x / t) ^ 6 ≤ 1 := pow_le_one₀ hu0 hu1
      have hsq : (Work.EllipticEst.Core.i0Aux.etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := by
        simp only [Work.EllipticEst.Core.i0Aux.etaT]; ring
      calc (Work.EllipticEst.Core.i0Aux.etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := hsq
        _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hu6 (sq_nonneg x)
        _ = x ^ 2 := by ring
    have hInt1 : IntervalIntegrable
        (fun x : ℝ => (Work.EllipticEst.Core.i0Aux.etaT t x) ^ 2) volume 0 t := by
      apply Continuous.intervalIntegrable
      simp only [Work.EllipticEst.Core.i0Aux.etaT]
      fun_prop
    have hInt2 : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 t :=
      (continuous_id.pow 2).intervalIntegrable 0 t
    have hmono := intervalIntegral.integral_mono_on (le_of_lt ht) hInt1 hInt2 hpt1
    have hv : (∫ x in (0 : ℝ)..t, x ^ 2) = t ^ 3 / 3 := by
      rw [integral_pow]
      norm_num
    rwa [hv] at hmono
  · -- `∫_0^t (η'')² ≤ 36/t`: pointwise `(η'')² ≤ 36/t²`, then `∫_0^t 36/t² = 36/t`.
    have hpt2 : ∀ x ∈ Set.Icc (0 : ℝ) t,
        (Work.EllipticEst.Core.i0Aux.etaT'' t x) ^ 2 ≤ 36 / t ^ 2 := by
      intro x hx
      obtain ⟨hx0, hxt⟩ := hx
      have hxt' : x / t ≤ 1 := (div_le_one ht).mpr hxt
      have hx0' : 0 ≤ x / t := div_nonneg hx0 (le_of_lt ht)
      have hu1 : 1 - x / t ≤ 1 := by linarith
      have hv0 : -1 ≤ 2 * (x / t) - 1 := by linarith
      have hv1 : 2 * (x / t) - 1 ≤ 1 := by linarith
      have hu2 : (1 - x / t) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨by linarith, hu1⟩)
      have hv2 : (2 * (x / t) - 1) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨hv0, hv1⟩)
      have hprod : (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 :=
        calc (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 * 1 :=
              mul_le_mul hu2 hv2 (sq_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hsq : (Work.EllipticEst.Core.i0Aux.etaT'' t x) ^ 2
          = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := by
        simp only [Work.EllipticEst.Core.i0Aux.etaT'']; ring
      calc (Work.EllipticEst.Core.i0Aux.etaT'' t x) ^ 2
          = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := hsq
        _ ≤ (36 / t ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left hprod (div_nonneg (by norm_num) (sq_nonneg t))
        _ = 36 / t ^ 2 := by ring
    have hIntA : IntervalIntegrable
        (fun x : ℝ => (Work.EllipticEst.Core.i0Aux.etaT'' t x) ^ 2) volume 0 t := by
      apply Continuous.intervalIntegrable
      simp only [Work.EllipticEst.Core.i0Aux.etaT'']
      fun_prop
    have hIntB : IntervalIntegrable (fun x : ℝ => (36 / t ^ 2 : ℝ)) volume 0 t :=
      continuous_const.intervalIntegrable 0 t
    have hmono := intervalIntegral.integral_mono_on (le_of_lt ht) hIntA hIntB hpt2
    have hv : (∫ x in (0 : ℝ)..t, (36 / t ^ 2 : ℝ)) = 36 / t := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      field_simp
    rwa [hv] at hmono

end Work.EllipticEst.Core.i0Aux.EndpointValues
