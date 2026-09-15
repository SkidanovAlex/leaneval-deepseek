import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le

open Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Commons.Analysis.Asymptotics

theorem eventual_const_add_mul_exp_neg_sqrtLog_le_div_log_pow {A c B D : ℝ} (hA : 0 < A)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      B + D * x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤ x / (Real.log x) ^ A := by
  have hc2 : 0 < c / 2 := by linarith
  -- First part: `B * (log x)^A / x → 0` as `x → ∞`.
  have hT1 : Tendsto (fun x : ℝ => B * ((Real.log x) ^ A / x)) atTop (nhds 0) := by
    have h : (fun x : ℝ => (Real.log x) ^ A) =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 1)
    have h' : Tendsto (fun x : ℝ => (Real.log x) ^ A / x ^ (1 : ℝ)) atTop (nhds 0) :=
      h.tendsto_div_nhds_zero
    have h'' : Tendsto (fun x : ℝ => (Real.log x) ^ A / x) atTop (nhds 0) := by
      simpa using h'
    simpa using h''.const_mul B
  have h1 : ∀ᶠ x : ℝ in atTop, B * ((Real.log x) ^ A / x) ≤ 1 / 2 :=
    hT1.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  -- Second part: `D * (log x)^A * exp(-(c/2) * sqrt(log x)) → 0` as `x → ∞`.
  have hT2u : Tendsto (fun u : ℝ => u ^ (2 * A) * Real.exp (-(c / 2) * u)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * A) (c / 2) hc2
  have hsq : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hT2comp : Tendsto (fun x : ℝ =>
      (Real.sqrt (Real.log x)) ^ (2 * A) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log x))) atTop (nhds 0) :=
    hT2u.comp hsq
  have heq : (fun x : ℝ =>
      (Real.sqrt (Real.log x)) ^ (2 * A) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log x)))
      =ᶠ[atTop] (fun x : ℝ =>
        (Real.log x) ^ A * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have : (Real.sqrt (Real.log x)) ^ (2 * A) = (Real.log x) ^ A := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlog0]
      ring_nf
    rw [this]
  have hT2x : Tendsto (fun x : ℝ =>
      (Real.log x) ^ A * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) atTop (nhds 0) :=
    hT2comp.congr' heq
  have hT2 : Tendsto (fun x : ℝ =>
      D * ((Real.log x) ^ A * Real.exp (-(c / 2) * Real.sqrt (Real.log x)))) atTop (nhds 0) := by
    simpa using hT2x.const_mul D
  have h2 : ∀ᶠ x : ℝ in atTop,
      D * ((Real.log x) ^ A * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) ≤ 1 / 2 :=
    hT2.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  -- Combine.
  have hmain : ∀ᶠ x : ℝ in atTop,
      B + D * x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤ x / (Real.log x) ^ A := by
    filter_upwards [h1, h2, eventually_ge_atTop (2 : ℝ)] with x hx1 hx2 hxge
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hpowpos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
    have hsum : B * ((Real.log x) ^ A / x) +
        D * ((Real.log x) ^ A * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) ≤ 1 := by
      linarith
    have hfac : 0 < x / (Real.log x) ^ A := div_pos hxpos hpowpos
    have hmul := mul_le_mul_of_nonneg_left hsum hfac.le
    have heq2 : x / (Real.log x) ^ A *
        (B * ((Real.log x) ^ A / x) +
          D * ((Real.log x) ^ A * Real.exp (-(c / 2) * Real.sqrt (Real.log x))))
        = B + D * x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
      field_simp [hxpos.ne', hpowpos.ne']
    rw [heq2, mul_one] at hmul
    exact hmul
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hmain
  exact ⟨x₀, hx₀⟩

end Commons.Analysis.Asymptotics