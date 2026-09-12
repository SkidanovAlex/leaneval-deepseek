import Submission.Serre
import Submission.SerreExample
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Potential-theoretic definitions (clean)

Definitions shared by the arithmeticity development (`Submission.SerreArithmetic`)
and its proof modules: the logarithmic potential of a measure on ℝ at a complex
point, the interval log-capacity, and Serre's constant.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.PotentialDefs

open Submission.Serre
open Submission.SerreExample

/-- The logarithmic potential `U^μ(z) = ∫ −log‖z−t‖ dμ(t)` (classical sign
convention of Smith's paper). -/
noncomputable def logPotential (μ : Measure ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, -Real.log ‖z - (t : ℂ)‖ ∂μ

/-- `−log` of the capacity `(d−c)/4` of the interval `[c,d]`. -/
noncomputable def logCap (c d : ℝ) : ℝ := -Real.log ((d - c) / 4)

/-- The constant of Serre's example (value of `U^μ + γ·log|x|` on `[a,b]`). -/
noncomputable def serreConstant : ℝ :=
  -Real.log ((bSerre - aSerre) / 4) +
    gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4)

/-- The absolute value of a real number, viewed in ℂ, is its real absolute value. -/
lemma norm_complex_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simpa using (Complex.norm_real r)

/-- For real `z`, the log potential integrand depends only on the real distance. -/
lemma log_norm_sub_ofReal (z x : ℝ) :
    -Real.log ‖(z : ℂ) - (x : ℂ)‖ = -Real.log |z - x| := by
  congr 1
  congr 1
  rw [← Complex.ofReal_sub, norm_complex_ofReal]

end Submission.PotentialDefs
