import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Elementary log-kernel identities (interval integrals of `1/r`)

Small lemmas used throughout the three_pages machinery: for `0 < s ≤ L`,
`∫_s^L dr/r = log L − log s`, so for a single root at distance `ρ` from `x`,
`(1/n)·∫_ρ^δ dr/r = (1/n)·(log δ − log ρ)`.
-/

noncomputable section

open scoped Real
open MeasureTheory

namespace Submission.LogKernel

/-- `∫_s^L r⁻¹ dr = log L − log s` for `0 < s ≤ L`. -/
theorem interval_integral_inv_log {s L : ℝ} (hs : 0 < s) (hsL : s ≤ L) :
    (∫ r in s..L, r⁻¹) = Real.log L - Real.log s := by
  have hderiv : ∀ x : ℝ, x ∈ Set.Ioo s L → HasDerivAt Real.log x⁻¹ x := by
    intro x hx
    exact Real.hasDerivAt_log (ne_of_gt (lt_trans hs hx.1))
  have hsubset : Set.Icc s L ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx
    simp
    exact ne_of_gt (lt_of_lt_of_le hs hx.1)
  have hcont : ContinuousOn Real.log (Set.Icc s L) := Real.continuousOn_log.mono hsubset
  have hint : IntervalIntegrable (fun r : ℝ => r⁻¹) volume s L := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsL]
    have hne : ∀ r : ℝ, r ∈ Set.Icc s L → r ≠ 0 := fun r hr => ne_of_gt (lt_of_lt_of_le hs hr.1)
    have hcont1 : ContinuousOn (fun r : ℝ => r⁻¹) (Set.Icc s L) := continuousOn_id.inv₀ hne
    exact hcont1.integrableOn_compact isCompact_Icc
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := Real.log)
    (f' := fun r : ℝ => r⁻¹) hsL hcont hderiv hint)

/-- `∫_s^L (1/r) dr = log L − log s` for `0 < s ≤ L`. -/
theorem interval_integral_one_div_log {s L : ℝ} (hs : 0 < s) (hsL : s ≤ L) :
    (∫ r in s..L, (1 : ℝ) / r) = Real.log L - Real.log s := by
  simpa [one_div] using (interval_integral_inv_log (s := s) (L := L) hs hsL)

/-- Symmetric form: `log L − log s = ∫_s^L dr/r` for `0 < s ≤ L`. -/
theorem log_sub_eq_interval_integral_inv {s L : ℝ} (hs : 0 < s) (hsL : s ≤ L) :
    Real.log L - Real.log s = (∫ r in s..L, r⁻¹) :=
  (interval_integral_inv_log hs hsL).symm

/-- For `0 < ρ ≤ δ`, `(1/n)·(log δ − log ρ) = (1/n)·∫_ρ^δ dr/r`. -/
theorem one_div_n_mul_log_sub {n : ℕ} {ρ δ : ℝ} (hρ : 0 < ρ) (hρδ : ρ ≤ δ) :
    (1 / (n : ℝ)) * (Real.log δ - Real.log ρ) =
      (1 / (n : ℝ)) * (∫ r in ρ..δ, r⁻¹) := by
  rw [log_sub_eq_interval_integral_inv hρ hρδ]

end Submission.LogKernel
