import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.SelfBound` — the elementary scaled-integral bound

For `-1 < c` and `|φ| ≤ B` on `(0,1]`, the scaled integral `∫₀¹ v^c·φ v dv` is bounded by
`B/(c+1) = B·∫₀¹ v^c dv`.  The proof is `intervalIntegral.norm_integral_le_of_norm_le`
(whose domination hypothesis is only required on `Ioc 0 1`, so the (irrelevant) values of `φ`
at `v = 0` are never used) together with `integral_rpow`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SBpsiP

set_option autoImplicit false

/-- **The scaled-integral bound.**  If `-1 < c` and `|φ v| ≤ B` for `v ∈ (0,1]`, then
`|∫₀¹ v^c·φ v dv| ≤ B/(c+1)`. -/
theorem J_bound_self {c B : ℝ} (hc : -1 < c) (hB : 0 ≤ B) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Ioc (0 : ℝ) 1))
    (hφ : ∀ v ∈ Set.Ioc (0 : ℝ) 1, |φ v| ≤ B) :
    |∫ v in (0 : ℝ)..1, v ^ c * φ v| ≤ B / (c + 1) := by
  have hint : IntervalIntegrable (fun v : ℝ => B * v ^ c) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hc).const_mul B
  have hpt : ∀ v ∈ Set.Ioc (0 : ℝ) 1, ‖v ^ c * φ v‖ ≤ B * v ^ c := by
    intro v hv
    have hv0 : 0 < v := hv.1
    have hvc : (0 : ℝ) ≤ v ^ c := Real.rpow_nonneg hv0.le c
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hvc]
    calc v ^ c * |φ v| ≤ v ^ c * B := mul_le_mul_of_nonneg_left (hφ v hv) hvc
      _ = B * v ^ c := by ring
  have hmain : ‖∫ v in (0 : ℝ)..1, v ^ c * φ v‖ ≤ ∫ v in (0 : ℝ)..1, B * v ^ c :=
    intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall hpt) hint
  have hval : (∫ v in (0 : ℝ)..1, B * v ^ c) = B / (c + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hc), Real.one_rpow,
      Real.zero_rpow (by linarith : c + 1 ≠ 0)]
    ring
  rw [hval] at hmain
  rwa [Real.norm_eq_abs] at hmain

end Work.FTS_StreamBdry.SBpsiP
