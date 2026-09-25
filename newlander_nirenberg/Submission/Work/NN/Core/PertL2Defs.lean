/-
The weighted measure `e^{-φ} dz` on the flat model `ℂⁿ = Fin n → ℂ`, used to state the
`L²_φ` calculus of the perturbed `∂̄`-solvability lemma
`Work.NN.Core.exists_solution_of_pertBasicEstimate`.
-/
import Mathlib
import Submission.Work.NN.Assemble.L2Forms

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff ENNReal NNReal

namespace Work.NN.Core

/-- The weighted measure `e^{-φ} dz` on the flat model `ℂⁿ = Fin n → ℂ`. -/
noncomputable def wMeas (n : ℕ) (φ : Cn n → ℝ) : Measure (Cn n) :=
  volume.withDensity (fun z => (((Real.exp (-(φ z))).toNNReal : ℝ≥0) : ℝ≥0∞))

end Work.NN.Core
