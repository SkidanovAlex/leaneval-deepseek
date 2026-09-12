import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shared definitions of the converse/arithmeticity layer (sorry-free)

`ArithmeticOn`, `rootSumComplex`, `rootMeanReal` used by both the contract hub
(`Submission/Converse.lean`) and the arithmeticity proof
(`Submission/ArithmeticAssembly.lean`) — kept here, free of sorries, to avoid
import cycles.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.Notions

open AlgebraicIntegers

/-- Arithmeticity of a (probability) measure `μ` on the real line: for every
nonzero integer polynomial `Q`, `∫ log|Q(x)| dμ(x) ≥ 0`. -/
def ArithmeticOn (μ : Measure ℝ) : Prop :=
  ∀ Q : Polynomial ℤ, Q ≠ 0 →
    0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂μ

/-- The sum of the complex roots of `R` (each with multiplicity). -/
noncomputable def rootSumComplex (R : Polynomial ℤ) : ℂ :=
  ((R.map (algebraMap ℤ ℚ)).aroots ℂ).sum

/-- The real mean of the complex roots of `R` (each counted with multiplicity):
the real part of the root sum divided by the number of roots (= `natDegree` for a
nonzero `R`).  This is what weak-* convergence of the root counting measures
`(1/n)·Σδ_root` gives: the root *means* converge to the first moment `∫ x dμ`.
-/
noncomputable def rootMeanReal (R : Polynomial ℤ) : ℝ :=
  (rootSumComplex R).re / (R.natDegree : ℝ)

end Submission.Notions
