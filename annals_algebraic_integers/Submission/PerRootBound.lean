import Submission.PotentialDefs
import Submission.Serre
import Submission.SerreExample
import Submission.SerreMean
import Submission.SupportConcentration
import Submission.SerrePotentialBound
import Submission.SerreLogMomentPos
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Per-root bound for the arithmeticity assembly (C2)

Let `μ := serreMeasure gSerre aSerre bSerre`.  For every complex `z ≠ 0`,

    ∫ x, log‖(x:ℂ) − z‖ ∂μ ≥ γ·log‖z‖ − serreConstant

and (A4-num) `0 ≤ ∫ x, log‖(x:ℂ)‖ ∂μ` for the zero root.

## Route
1. Per-root potential identity: `logPotential μ z = ∫ x, −log‖z − (x:ℂ)‖ ∂μ`
   and `‖z − (x:ℂ)‖ = ‖(x:ℂ) − z‖` (modulus symmetric), so
       ∫ x, log‖(x:ℂ) − z‖ ∂μ = −logPotential μ z
   (as real-valued integrals; provide integrability of the log-norm integrand
   against the compactly-supported atom-free `μ` — the established pattern).
2. By `Submission.SerrePotentialBound.serre_potential_bound hz` (A3):
       logPotential μ z + γ·log‖z‖ ≤ serreConstant
   hence `−logPotential μ z ≥ γ·log‖z‖ − serreConstant` (linarith).
3. Combine.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.PerRootBound

open Submission.PotentialDefs
open Submission.Serre
open Submission.SerreExample
open Submission.SerrePotentialBound

/-- `∫ log‖(x:ℂ) − z‖ dμ = −U^μ(z)` (per-root potential identity). -/
lemma integral_log_norm_sub_eq_neg_logPotential {z : ℂ} :
    (∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre) =
      -logPotential (serreMeasure gSerre aSerre bSerre) z := by
  unfold logPotential
  calc
    (∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre)
        = (∫ x : ℝ, Real.log ‖z - (x : ℂ)‖ ∂serreMeasure gSerre aSerre bSerre) := by
            -- modulus is symmetric: ‖(x:ℂ) − z‖ = ‖z − (x:ℂ)‖
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            congr 1
            rw [norm_sub_rev (x : ℂ) z]
    _ = -((∫ x : ℝ, -Real.log ‖z - (x : ℂ)‖ ∂serreMeasure gSerre aSerre bSerre)) := by
            -- ∫ −f = −∫ f (holds for the Bochner integral without further hypotheses)
            rw [MeasureTheory.integral_neg]
            simp
    _ = -logPotential (serreMeasure gSerre aSerre bSerre) z := by
            rfl

/-- (C2) Per-root bound for nonzero roots. -/
theorem per_root_bound {z : ℂ} (hz : z ≠ 0) :
    (∫ x : ℝ, Real.log ‖(x : ℂ) - z‖ ∂serreMeasure gSerre aSerre bSerre) ≥
      gSerre * Real.log ‖z‖ - serreConstant := by
  -- per-root identity: ∫ log‖(x:ℂ) − z‖ dμ = −U^μ(z)
  rw [integral_log_norm_sub_eq_neg_logPotential]
  -- potential bound (A3): U^μ(z) + γ·log‖z‖ ≤ serreConstant
  have hA3 := serre_potential_bound hz
  linarith

/-- (C2) Zero-root bound (log-moment nonnegativity). -/
theorem zero_root_bound :
    0 ≤ (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂serreMeasure gSerre aSerre bSerre) := by
  exact le_of_lt Submission.SerreLogMomentPos.serre_log_moment_pos

end Submission.PerRootBound
