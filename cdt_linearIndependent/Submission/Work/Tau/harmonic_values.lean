import Mathlib
import Submission.Work.Tau.defs

/-!
# Exact values of the `harmonicFun` integrals for `w = 7/4` and `w = 2`

`harmonicFun w t = Σ_{h ∈ Icc 1 ⌊(t-1)/max 1 w⌋} 1/h` vanishes for `t ≤ max 1 w`, so for
`ξ ∈ {7/4, 2}` (both `≥ 1`, so `max 1 ξ = ξ`) the integral `∫_ξ^v harmonicFun ξ` equals
`∫_1^v harmonicFun ξ`, and the closed form `Submission.CDT.IntegratedLcm.integral_harmonicFun`
evaluates the latter as a finite sum.
-/

namespace Work.Tau

open MeasureTheory intervalIntegral
open Submission.CDT.IntegratedLcm

/-- `∫_1^a harmonicFun ξ = 0` for `1 ≤ a ≤ ξ`, `1 ≤ ξ`: the integrand vanishes on `[1, a]`. -/
theorem integral_harmonicFun_eq_zero (ξ a : ℝ) (hξ : 1 ≤ ξ) (ha : 1 ≤ a) (haξ : a ≤ ξ) :
    (∫ t in (1:ℝ)..a, harmonicFun ξ t) = 0 := by
  have hEq : Set.EqOn (harmonicFun ξ) (fun _ => (0:ℝ)) (Set.uIcc 1 a) := by
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    exact Submission.CDT.FineHolonomy.harmonicFun_eq_zero_of_le ξ hξ ⟨ht.1, le_trans ht.2 haξ⟩
  rw [intervalIntegral.integral_congr hEq]
  simp

/-- `∫_a^v harmonicFun ξ = ∫_1^v harmonicFun ξ` when `1 ≤ a ≤ ξ` and `a ≤ v`. -/
theorem integral_harmonicFun_eq_of_le (ξ a v : ℝ) (hξ : 1 ≤ ξ) (ha : 1 ≤ a) (haξ : a ≤ ξ)
    (hav : a ≤ v) :
    (∫ t in a..v, harmonicFun ξ t) = ∫ t in (1:ℝ)..v, harmonicFun ξ t := by
  have h0 := integral_add_adjacent_intervals
    (Submission.CDT.FineHolonomy.intervalIntegrable_harmonicFun' ξ 1 a (by norm_num) ha)
    (Submission.CDT.FineHolonomy.intervalIntegrable_harmonicFun' ξ a v ha hav)
  rw [integral_harmonicFun_eq_zero ξ a hξ ha haξ, zero_add] at h0
  linarith [h0]

theorem harmonic_values :
    (∫ t in (7 / 4 : ℝ)..17, Submission.CDT.IntegratedLcm.harmonicFun (7 / 4) t) = 37187 / 1260
    ∧ (∫ t in (2 : ℝ)..14, Submission.CDT.IntegratedLcm.harmonicFun 2 t) = 397 / 20 := by
  constructor
  · rw [integral_harmonicFun_eq_of_le (7/4) (7/4) 17 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]
    rw [integral_harmonicFun 17 (7/4) (by norm_num)]
    norm_num [Finset.sum_Icc_succ_top]
  · rw [integral_harmonicFun_eq_of_le 2 2 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    rw [integral_harmonicFun 14 2 (by norm_num)]
    norm_num [Finset.sum_Icc_succ_top]

end Work.Tau
